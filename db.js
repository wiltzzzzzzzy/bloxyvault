// db.js
// PostgreSQL persistence layer for BloxyVault's multiplayer server.
// This file only ever runs server-side (required by server.js) - nothing
// here is ever sent to or reachable from the browser, and DATABASE_URL
// itself only ever lives in Railway's environment variables, never in code.
//
// Design: server.js keeps its existing in-memory `users` Map as a
// write-through cache (unchanged game logic, same synchronous balance
// checks it already had), and calls into this file to persist state to
// Postgres alongside every mutation. Postgres is the durable source of
// truth; memory is just a fast, always-current mirror of it.

const { Pool } = require('pg');

if (!process.env.DATABASE_URL) {
  throw new Error(
    "DATABASE_URL is not set. Add the PostgreSQL plugin to this Railway project, " +
    "then reference its DATABASE_URL into this service's Variables tab."
  );
}

// Railway's internal Postgres connections (service-to-service, same project)
// don't need SSL. If DATABASE_URL ever points somewhere external (e.g. the
// public proxy URL, or a local dev DB you're testing against), enable it
// automatically instead of needing a separate flag to remember.
const useSSL = /sslmode=require/i.test(process.env.DATABASE_URL) || process.env.PGSSL === 'true';

const pool = new Pool({
  connectionString: process.env.DATABASE_URL,
  ssl: useSSL ? { rejectUnauthorized: false } : false,
});

// A dropped idle connection must never crash the whole process - the pool
// recovers on the next query either way.
pool.on('error', (err) => {
  console.error('[db] Unexpected error on idle Postgres client:', err);
});

// ---------------------------------------------------------------------------
// Schema - created on boot if it doesn't already exist. Safe to run on every
// deploy (IF NOT EXISTS everywhere), so there's no separate migration step
// to remember.
// ---------------------------------------------------------------------------
async function initSchema() {
  await pool.query(`
    CREATE TABLE IF NOT EXISTS users (
      username        TEXT PRIMARY KEY,
      coins           BIGINT NOT NULL DEFAULT 0 CHECK (coins >= 0),
      stats_wagered   BIGINT NOT NULL DEFAULT 0,
      stats_won       BIGINT NOT NULL DEFAULT 0,
      stats_lost      BIGINT NOT NULL DEFAULT 0,
      created_at      TIMESTAMPTZ NOT NULL DEFAULT now(),
      updated_at      TIMESTAMPTZ NOT NULL DEFAULT now()
    );
  `);

  await pool.query(`
    CREATE TABLE IF NOT EXISTS inventory_items (
      username     TEXT NOT NULL REFERENCES users(username) ON DELETE CASCADE,
      catalog_id   TEXT NOT NULL,
      qty          INTEGER NOT NULL DEFAULT 0 CHECK (qty >= 0),
      PRIMARY KEY (username, catalog_id)
    );
  `);

  await pool.query(`
    CREATE TABLE IF NOT EXISTS withdraw_requests (
      id                TEXT PRIMARY KEY,
      username          TEXT NOT NULL REFERENCES users(username),
      items             JSONB NOT NULL,
      status            TEXT NOT NULL DEFAULT 'pending'
                          CHECK (status IN ('pending','fulfilled','rejected','cancelled')),
      requested_at      TIMESTAMPTZ NOT NULL DEFAULT now(),
      resolved_at       TIMESTAMPTZ,
      actually_removed  JSONB
    );
  `);

  // A waiting Coinflip lobby escrows the creator's items out of their
  // inventory the instant it's created (see handleCoinflipCreate), well
  // before anyone actually joins it. Without persisting the lobby itself,
  // a server restart while it's still sitting there waiting would wipe it
  // from memory with no record of who those escrowed items belong to -
  // they'd just be gone, even though nobody ever joined and "won" them.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS coinflip_lobbies (
      id            TEXT PRIMARY KEY,
      creator       TEXT NOT NULL REFERENCES users(username),
      side          TEXT NOT NULL,
      items         JSONB NOT NULL,
      locked        BOOLEAN,
      created_at    TIMESTAMPTZ NOT NULL DEFAULT now()
    );
  `);
  // Migration for any database that already had this table from before the
  // normal/duped pet-lock feature existed - CREATE TABLE IF NOT EXISTS
  // alone won't add a missing column to an already-existing table.
  await pool.query(`ALTER TABLE coinflip_lobbies ADD COLUMN IF NOT EXISTS locked BOOLEAN;`);

  await pool.query(`
    CREATE TABLE IF NOT EXISTS transactions (
      id               BIGSERIAL PRIMARY KEY,
      username         TEXT NOT NULL REFERENCES users(username),
      type             TEXT NOT NULL,
      amount           BIGINT NOT NULL,
      balance_before   BIGINT NOT NULL,
      balance_after    BIGINT NOT NULL,
      items_delta      JSONB,
      reason           TEXT,
      admin_username   TEXT,
      created_at       TIMESTAMPTZ NOT NULL DEFAULT now()
    );
  `);
  await pool.query(`CREATE INDEX IF NOT EXISTS idx_transactions_username ON transactions(username, created_at DESC);`);
  await pool.query(`CREATE INDEX IF NOT EXISTS idx_withdraw_status ON withdraw_requests(status);`);

  // Coinflip history - was previously only tracked client-side in a
  // browser-local array (cfMyHistory), which is why it never survived a
  // restart/redeploy (and didn't even survive a page reload). One row per
  // resolved flip, from both participants' perspective at once - the query
  // that reads this back does the per-viewer transform (who's "opponent",
  // whether "you" won, etc.), same as the client used to compute locally.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS coinflip_history (
      id               BIGSERIAL PRIMARY KEY,
      creator          TEXT NOT NULL,
      joiner           TEXT NOT NULL,
      creator_side     TEXT NOT NULL,
      joiner_side      TEXT NOT NULL,
      creator_items    JSONB NOT NULL,
      joiner_items     JSONB NOT NULL,
      creator_value    BIGINT NOT NULL,
      joiner_value     BIGINT NOT NULL,
      result           TEXT NOT NULL,
      winner           TEXT NOT NULL,
      resolved_at      TIMESTAMPTZ NOT NULL DEFAULT now()
    );
  `);
  await pool.query(`CREATE INDEX IF NOT EXISTS idx_cf_history_creator ON coinflip_history(creator, resolved_at DESC);`);
  await pool.query(`CREATE INDEX IF NOT EXISTS idx_cf_history_joiner ON coinflip_history(joiner, resolved_at DESC);`);

  console.log('[db] Schema ready.');
}

// ---------------------------------------------------------------------------
// Boot-time loads - populate server.js's in-memory Map/array from Postgres
// before the server starts accepting connections.
// ---------------------------------------------------------------------------

// Returns a Map in the exact shape server.js's `users` Map already expects:
// username -> { coins, inventory: {catalogId: qty}, stats: {wagered, won, lost} }
async function loadAllUsers() {
  const usersRes = await pool.query('SELECT username, coins, stats_wagered, stats_won, stats_lost FROM users');
  const invRes = await pool.query('SELECT username, catalog_id, qty FROM inventory_items WHERE qty > 0');

  const map = new Map();
  for (const row of usersRes.rows) {
    map.set(row.username, {
      coins: Number(row.coins),
      inventory: {},
      stats: { wagered: Number(row.stats_wagered), won: Number(row.stats_won), lost: Number(row.stats_lost) },
    });
  }
  for (const row of invRes.rows) {
    const u = map.get(row.username);
    if (u) u.inventory[row.catalog_id] = row.qty;
  }
  return map;
}

// Returns pending withdrawal requests in the exact shape server.js's
// `withdrawRequests` array already expects.
async function loadPendingWithdrawRequests() {
  const res = await pool.query(
    `SELECT id, username, items, status, requested_at, actually_removed
     FROM withdraw_requests WHERE status = 'pending' ORDER BY requested_at ASC`
  );
  return res.rows.map((r) => ({
    id: r.id,
    username: r.username,
    items: r.items,
    status: r.status,
    requestedAt: new Date(r.requested_at).getTime(),
    actuallyRemoved: r.actually_removed || undefined,
  }));
}

// Returns still-waiting Coinflip lobbies in the exact shape server.js's
// `cfLobbies` array already expects - every row here is a lobby that was
// created but never joined/cancelled, so its items are still escrowed.
async function loadPendingCoinflipLobbies() {
  const res = await pool.query(
    `SELECT id, creator, side, items, locked FROM coinflip_lobbies ORDER BY created_at ASC`
  );
  return res.rows.map((r) => ({
    id: r.id,
    creator: r.creator,
    side: r.side,
    items: r.items,
    // null (a lobby persisted from before this feature existed) is
    // deliberately left as undefined here, not coerced to false - see
    // joinItemsMatchLockedLobby in server.js, which treats undefined as
    // "legacy lobby, no pet-identity restriction" rather than "unlocked".
    locked: r.locked == null ? undefined : r.locked,
  }));
}

// ---------------------------------------------------------------------------
// Writes
// ---------------------------------------------------------------------------

// Inserts a brand-new user row (idempotent - ON CONFLICT DO NOTHING, since
// ensureUser() in server.js is the caller and only fires this the first
// time it creates someone in memory, but a second caller racing in is fine).
async function insertNewUser(username, coins, stats) {
  await pool.query(
    `INSERT INTO users (username, coins, stats_wagered, stats_won, stats_lost)
     VALUES ($1, $2, $3, $4, $5)
     ON CONFLICT (username) DO NOTHING`,
    [username, coins, stats.wagered, stats.won, stats.lost]
  );
}

// The main persistence call: writes a user's current coins/stats, upserts
// only the specific inventory rows that changed (not the whole inventory -
// keeps this cheap even for accounts with a lot of items), and - if a txn
// is supplied - writes one immutable transaction/audit row. All of it in a
// single real Postgres transaction, so a crash mid-write can never leave
// coins updated but the inventory or audit row missing, and the audit row
// is only ever written alongside a successfully committed balance change.
//
// `user` is the in-memory user object AFTER the mutation already happened
// (server.js updates memory synchronously first, exactly as before - this
// just mirrors that already-decided state into Postgres).
//
// `txn` (optional): {
//   type: string,                 // 'game_wager' | 'game_resolve' | 'tip_send' | ...
//   amount: number,                // coin delta, +/- (0 for item-only txns)
//   balanceBefore: number,
//   balanceAfter: number,
//   itemsTouched: string[],        // catalogIds whose qty changed - current qty is read from `user.inventory`
//   reason: string,
//   adminUsername: string,
// }
async function persistUserState(username, user, txn) {
  const client = await pool.connect();
  try {
    await client.query('BEGIN');

    const upd = await client.query(
      `UPDATE users SET coins = $2, stats_wagered = $3, stats_won = $4, stats_lost = $5, updated_at = now()
       WHERE username = $1`,
      [username, user.coins, user.stats.wagered, user.stats.won, user.stats.lost]
    );
    if (upd.rowCount === 0) {
      await client.query(
        `INSERT INTO users (username, coins, stats_wagered, stats_won, stats_lost) VALUES ($1,$2,$3,$4,$5)`,
        [username, user.coins, user.stats.wagered, user.stats.won, user.stats.lost]
      );
    }

    if (txn && Array.isArray(txn.itemsTouched) && txn.itemsTouched.length) {
      for (const catalogId of txn.itemsTouched) {
        const qty = Math.max(0, user.inventory[catalogId] || 0);
        await client.query(
          `INSERT INTO inventory_items (username, catalog_id, qty) VALUES ($1,$2,$3)
           ON CONFLICT (username, catalog_id) DO UPDATE SET qty = $3`,
          [username, catalogId, qty]
        );
      }
    }

    if (txn) {
      await client.query(
        `INSERT INTO transactions (username, type, amount, balance_before, balance_after, items_delta, reason, admin_username)
         VALUES ($1,$2,$3,$4,$5,$6,$7,$8)`,
        [
          username,
          txn.type,
          Math.trunc(txn.amount || 0),
          Math.trunc(txn.balanceBefore != null ? txn.balanceBefore : user.coins),
          Math.trunc(txn.balanceAfter != null ? txn.balanceAfter : user.coins),
          txn.itemsTouched && txn.itemsTouched.length ? JSON.stringify(txn.itemsTouched) : null,
          txn.reason || null,
          txn.adminUsername || null,
        ]
      );
    }

    await client.query('COMMIT');
  } catch (err) {
    await client.query('ROLLBACK');
    console.error(`[db] Failed to persist state for ${username}:`, err);
    throw err;
  } finally {
    client.release();
  }
}

async function insertWithdrawRequest(req) {
  await pool.query(
    `INSERT INTO withdraw_requests (id, username, items, status, requested_at) VALUES ($1,$2,$3,$4, to_timestamp($5/1000.0))`,
    [req.id, req.username, JSON.stringify(req.items), req.status, req.requestedAt]
  );
}

async function insertCoinflipLobby(lobby) {
  await pool.query(
    `INSERT INTO coinflip_lobbies (id, creator, side, items, locked) VALUES ($1,$2,$3,$4,$5)`,
    [lobby.id, lobby.creator, lobby.side, JSON.stringify(lobby.items), !!lobby.locked]
  );
}

// Called once a lobby is joined, cancelled, or otherwise resolved - it's no
// longer "waiting" at that point, so there's nothing left to protect against
// a restart for. Safe to call even if the row's already gone (e.g. a race
// between join and cancel) - just deletes 0 rows in that case.
async function deleteCoinflipLobby(id) {
  await pool.query(`DELETE FROM coinflip_lobbies WHERE id = $1`, [id]);
}

// Atomic status transition: only succeeds if the request is currently in
// `fromStatus`. Returns the updated row, or null if it had already been
// resolved by someone else (or another concurrent request) - the caller
// uses that to know whether it actually needs to act, so the same request
// can never be fulfilled/rejected/cancelled twice even under a race.
async function resolveWithdrawRequest(id, fromStatus, toStatus, actuallyRemoved) {
  const res = await pool.query(
    `UPDATE withdraw_requests SET status = $1, resolved_at = now(), actually_removed = $2
     WHERE id = $3 AND status = $4 RETURNING id`,
    [toStatus, actuallyRemoved ? JSON.stringify(actuallyRemoved) : null, id, fromStatus]
  );
  return res.rowCount > 0;
}

// Returns groups of usernames that differ only by capitalization - e.g.
// ["DTN_bgsi", "DTN_BGSI"] would come back as one cluster. Each cluster has
// 2+ members; usernames with no case-variant duplicate aren't included.
async function findDuplicateCaseClusters() {
  const res = await pool.query('SELECT username FROM users');
  const byLower = new Map();
  for (const { username } of res.rows) {
    const key = username.toLowerCase();
    if (!byLower.has(key)) byLower.set(key, []);
    byLower.get(key).push(username);
  }
  return [...byLower.values()].filter((cluster) => cluster.length > 1);
}

// Merges every username in `variants` into `canonicalUsername`, atomically,
// with no data loss:
//   - coins: MAX across variants (not summed - two accidental duplicates
//     both created at STARTING_BALANCE, or both independently topped up by
//     the same self-healing logic like DTN_BGSI's 99x/2B seed, would double
//     count if summed even though nothing extra was actually earned).
//   - inventory: MAX per item, same reasoning - the union of everything any
//     variant owned, without inflating an item both variants happened to
//     share.
//   - stats (wagered/won/lost): SUMMED - these are cumulative counters of
//     genuinely distinct real actions, so two real histories combining is
//     correct, not a duplication.
//   - withdrawal requests, transactions, and coinflip history: every row
//     is re-pointed to the canonical username, not duplicated or dropped -
//     the full audit trail survives under one identity.
// `canonicalUsername` does not need to already exist in `variants` - if
// Roblox's real casing doesn't match any current duplicate, this creates it
// fresh with the merged totals.
async function mergeCasedDuplicates(canonicalUsername, variants) {
  const client = await pool.connect();
  try {
    await client.query('BEGIN');

    const usersRes = await client.query('SELECT username, coins, stats_wagered, stats_won, stats_lost FROM users WHERE username = ANY($1)', [variants]);
    if (usersRes.rows.length < 2) { await client.query('ROLLBACK'); return null; } // nothing to merge after all

    const invRes = await client.query('SELECT username, catalog_id, qty FROM inventory_items WHERE username = ANY($1)', [variants]);

    const mergedCoins = Math.max(...usersRes.rows.map((r) => Number(r.coins)));
    const mergedWagered = usersRes.rows.reduce((s, r) => s + Number(r.stats_wagered), 0);
    const mergedWon = usersRes.rows.reduce((s, r) => s + Number(r.stats_won), 0);
    const mergedLost = usersRes.rows.reduce((s, r) => s + Number(r.stats_lost), 0);

    const mergedInventory = {}; // catalogId -> max qty across variants
    for (const row of invRes.rows) {
      mergedInventory[row.catalog_id] = Math.max(mergedInventory[row.catalog_id] || 0, row.qty);
    }

    // Upsert the canonical row with the merged totals.
    const upd = await client.query(
      `UPDATE users SET coins = $2, stats_wagered = $3, stats_won = $4, stats_lost = $5, updated_at = now() WHERE username = $1`,
      [canonicalUsername, mergedCoins, mergedWagered, mergedWon, mergedLost]
    );
    if (upd.rowCount === 0) {
      await client.query(
        `INSERT INTO users (username, coins, stats_wagered, stats_won, stats_lost) VALUES ($1,$2,$3,$4,$5)`,
        [canonicalUsername, mergedCoins, mergedWagered, mergedWon, mergedLost]
      );
    }

    for (const [catalogId, qty] of Object.entries(mergedInventory)) {
      await client.query(
        `INSERT INTO inventory_items (username, catalog_id, qty) VALUES ($1,$2,$3)
         ON CONFLICT (username, catalog_id) DO UPDATE SET qty = $3`,
        [canonicalUsername, catalogId, qty]
      );
    }

    const others = variants.filter((v) => v !== canonicalUsername);
    if (others.length) {
      // Re-point every historical record so nothing is lost or orphaned -
      // just relabeled under the one identity that now owns everything.
      await client.query(`UPDATE withdraw_requests SET username = $1 WHERE username = ANY($2)`, [canonicalUsername, others]);
      await client.query(`UPDATE transactions SET username = $1 WHERE username = ANY($2)`, [canonicalUsername, others]);
      await client.query(`UPDATE transactions SET admin_username = $1 WHERE admin_username = ANY($2)`, [canonicalUsername, others]);
      await client.query(`UPDATE coinflip_history SET creator = $1 WHERE creator = ANY($2)`, [canonicalUsername, others]);
      await client.query(`UPDATE coinflip_history SET joiner = $1 WHERE joiner = ANY($2)`, [canonicalUsername, others]);
      await client.query(`UPDATE coinflip_history SET winner = $1 WHERE winner = ANY($2)`, [canonicalUsername, others]);
      // Deleting the old rows cascades to their now-redundant inventory_items
      // rows automatically (ON DELETE CASCADE) - already fully accounted
      // for in mergedInventory above, so nothing is lost by the cascade.
      await client.query(`DELETE FROM users WHERE username = ANY($1)`, [others]);
    }

    // Leave a visible audit trail of the merge itself.
    await client.query(
      `INSERT INTO transactions (username, type, amount, balance_before, balance_after, items_delta, reason)
       VALUES ($1, 'account_merge', 0, $2, $2, $3, $4)`,
      [canonicalUsername, mergedCoins, JSON.stringify(Object.keys(mergedInventory)), `Merged duplicate case-variant accounts: ${variants.join(', ')}`]
    );

    await client.query('COMMIT');
    return { canonicalUsername, mergedFrom: others, coins: mergedCoins, itemCount: Object.keys(mergedInventory).length };
  } catch (err) {
    await client.query('ROLLBACK');
    throw err;
  } finally {
    client.release();
  }
}

// One row per resolved flip, both participants at once. Fire-and-forget
// from the caller, same pattern as persistUser - a coinflip's outcome has
// already been decided and broadcast by the time this is called, so a slow
// DB write here should never hold up the live result.
// Returns a user's most recent transactions, newest first - used by the
// admin lookup panel. Straightforward read against the existing Phase 1
// transactions table, no schema changes needed.
async function loadRecentTransactionsForUser(username, limit) {
  const res = await pool.query(
    `SELECT type, amount, balance_before, balance_after, items_delta, reason, admin_username, created_at
     FROM transactions WHERE username = $1 ORDER BY created_at DESC LIMIT $2`,
    [username, limit]
  );
  return res.rows.map((r) => ({
    type: r.type,
    amount: Number(r.amount),
    balanceBefore: Number(r.balance_before),
    balanceAfter: Number(r.balance_after),
    itemsDelta: r.items_delta,
    reason: r.reason,
    adminUsername: r.admin_username,
    timestamp: new Date(r.created_at).getTime(),
  }));
}

async function insertCoinflipHistory(row) {
  await pool.query(
    `INSERT INTO coinflip_history (creator, joiner, creator_side, joiner_side, creator_items, joiner_items, creator_value, joiner_value, result, winner)
     VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10)`,
    [
      row.creator, row.joiner, row.creatorSide, row.joinerSide,
      JSON.stringify(row.creatorItems), JSON.stringify(row.joinerItems),
      row.creatorValue, row.joinerValue, row.result, row.winner,
    ]
  );
}

// Returns a user's last `limit` flips already shaped exactly like the
// client's cfMyHistory entries ({opponent, myValue, oppValue, won,
// resultSide, timestamp, creator, joiner, creatorSide, joinerSide,
// creatorItems, joinerItems, youAreCreator}) - the "who's the opponent /
// did I win" transform happens here so the client doesn't need any new
// logic, just a place to drop the array in. Includes the full item lists
// and sides (not just the aggregate totals) so a flip loaded from here
// after a page refresh can still be rewatched via "View", the same as one
// that happened earlier in the current session.
async function loadCoinflipHistoryForUser(username, limit) {
  const res = await pool.query(
    `SELECT creator, joiner, creator_side, joiner_side, creator_items, joiner_items, creator_value, joiner_value, result, winner, resolved_at
     FROM coinflip_history WHERE creator = $1 OR joiner = $1
     ORDER BY resolved_at DESC LIMIT $2`,
    [username, limit]
  );
  return res.rows.map((r) => {
    const youAreCreator = r.creator === username;
    return {
      opponent: youAreCreator ? r.joiner : r.creator,
      myValue: youAreCreator ? Number(r.creator_value) : Number(r.joiner_value),
      oppValue: youAreCreator ? Number(r.joiner_value) : Number(r.creator_value),
      won: r.winner === username,
      resultSide: r.result,
      timestamp: new Date(r.resolved_at).getTime(),
      creator: r.creator,
      joiner: r.joiner,
      creatorSide: r.creator_side,
      joinerSide: r.joiner_side,
      creatorItems: typeof r.creator_items === 'string' ? JSON.parse(r.creator_items) : (r.creator_items || []),
      joinerItems: typeof r.joiner_items === 'string' ? JSON.parse(r.joiner_items) : (r.joiner_items || []),
      youAreCreator,
    };
  });
}

module.exports = {
  pool,
  initSchema,
  loadAllUsers,
  loadPendingWithdrawRequests,
  loadPendingCoinflipLobbies,
  insertNewUser,
  persistUserState,
  insertWithdrawRequest,
  resolveWithdrawRequest,
  insertCoinflipLobby,
  deleteCoinflipLobby,
  insertCoinflipHistory,
  loadCoinflipHistoryForUser,
  findDuplicateCaseClusters,
  mergeCasedDuplicates,
  loadRecentTransactionsForUser,
};

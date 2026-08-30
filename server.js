// BloxyVault multiplayer server
//
// Speaks the exact same message protocol the client already expects (it was
// originally built against a local mock that used this same shape, so the
// client needs zero changes beyond pointing window.BLOXYVAULT_SERVER_URL at
// this server's wss:// URL).
//
// State is entirely in-memory - it resets whenever this process restarts.
// That's fine for a practice/hobby multiplayer server; if you want accounts
// to survive restarts/deploys, swap the `users` Map for a real database
// later (the shape is simple: username -> {coins, inventory}).

const http = require('http');
const { WebSocketServer } = require('ws');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');
const db = require('./db');

const gameData = JSON.parse(fs.readFileSync(path.join(__dirname, 'gameData.json'), 'utf8'));
const { petCatalog, caseData, caseItems, casePools, modeConfigs, botNamesBattles } = gameData;

const STARTING_BALANCE = 0; // normal accounts start with nothing - no free coins on creation
const CASEBATTLE_ABANDON_MS = 5 * 60 * 1000; // if a creator walks away without calling bots or getting joined, clean it up after 5 minutes
const CASEBATTLE_FINISHED_DISPLAY_MS = 20 * 1000; // how long a finished battle stays visible in the list before it's removed
const ROUND_PACE_MS = 4300;        // must match the client's MOCK_ROUND_PACE_MS
const CF_MATCH_TOLERANCE = 0.10;   // coinflip stakes must be within ±10% of each other, matching the client's own join-range check

// Site owner - gets the coinflip rake (see resolveCoinflip below) and is the
// only account allowed to use the admin:lookup inventory viewer. Whoever
// this is effectively runs the house, so keep this accurate.
const ADMIN_USERNAME = 'tim_tim1345';

// Hand-out/giveaway account - not an admin, just a stocked account used to
// tip pets to players (see handleTipSend). Pre-loaded on first creation
// with one of every pet and a large coin balance so it never runs dry.
const GIVEAWAY_USERNAME = 'DTN_BGSI';
const GIVEAWAY_STARTING_BALANCE = 2000000000;

// A plain ledger account (not an admin, no special seeding/inventory like
// DTN_BGSI has) that the admin funds/drains manually via the coin
// management tool - just needs a distinct chat role color to be visually
// identifiable, same as the other two.
const STOCK_USERNAME = 'BloxyVault_Stock';

// Gates every testing-only, no-real-verification path in this file:
// /dev/skip-login (logs in as anyone with zero Roblox check) and
// account:reset. Both exist purely for local development and are OFF by
// default - Railway doesn't reliably set NODE_ENV on its own, so this
// deliberately requires an explicit opt-in rather than trusting an
// environment flag that might not be set. Only add ENABLE_DEV_BYPASS=true
// in Railway's Variables tab if you actually want these reachable (e.g. a
// separate staging deploy) - never on the real one.
// (debug:addTestCoins used to live here too - fully removed, not just
// gated, since normal users must have no path to free coins at all now.)
const ENABLE_DEV_BYPASS = process.env.ENABLE_DEV_BYPASS === 'true';
if (ENABLE_DEV_BYPASS) {
  console.warn('[security] ENABLE_DEV_BYPASS is ON - /dev/skip-login and account:reset are reachable. Do not leave this on in production.');
}

// ---------------------------------------------------------------------------
// Connection + account state
// ---------------------------------------------------------------------------
const users = new Map();          // username -> { coins, inventory: {catalogId: qty} }

// The Exchange's "coin to item" side now draws from real player-sold stock
// instead of minting any pet on demand. Starts completely empty - a pet
// only becomes buyable once someone actually sells one into it via
// handleExchangeSell. Shared across all players (not per-user).
const shopStock = {}; // catalogId -> qty available to buy
const socketToUsername = new Map(); // ws -> username
const usernameToSocket = new Map(); // username -> ws (most recent connection)

// ---------------------------------------------------------------------------
// Session tokens - proves a 'login' message actually came from someone who
// passed Roblox bio verification (or the dev skip-login bypass below), not
// just anyone who knows/guesses a username. In-memory like everything else
// here, so it resets on restart along with balances/inventory - swap for a
// real database if you need sessions to survive deploys.
// ---------------------------------------------------------------------------
const sessionTokens = new Map(); // token -> { username, expires }
const SESSION_TOKEN_TTL_MS = 7 * 24 * 60 * 60 * 1000; // 7 days, matches client-side persistence

function issueSessionToken(username) {
  const token = crypto.randomBytes(24).toString('hex');
  sessionTokens.set(token, { username, expires: Date.now() + SESSION_TOKEN_TTL_MS });
  return token;
}

function checkSessionToken(username, token) {
  if (!token) return false;
  const rec = sessionTokens.get(token);
  if (!rec) return false;
  if (rec.username !== username) return false;
  if (Date.now() > rec.expires) { sessionTokens.delete(token); return false; }
  return true;
}

// periodic cleanup so this map doesn't grow forever
setInterval(() => {
  const now = Date.now();
  for (const [token, rec] of sessionTokens) {
    if (now > rec.expires) sessionTokens.delete(token);
  }
}, 60 * 60 * 1000);

function ensureUser(username) {
  const isNewAccount = !users.has(username);
  const isGiveaway = username.toLowerCase() === GIVEAWAY_USERNAME.toLowerCase();

  if (isNewAccount) {
    const startingCoins = isGiveaway ? GIVEAWAY_STARTING_BALANCE : STARTING_BALANCE;
    const startingInventory = {};
    if (isGiveaway) for (const id of Object.keys(petCatalog)) startingInventory[id] = 99;
    users.set(username, { coins: startingCoins, inventory: startingInventory, stats: { wagered: 0, won: 0, lost: 0 }, specialRole: null, mutedUntil: 0 });
    if (isGiveaway) {
      // Seed both the balance AND the full inventory atomically in one go,
      // with a real transaction row - this only ever happens once, right
      // at creation, not on every touch (see below for why that matters).
      persistUser(username, { type: 'giveaway_seed', amount: startingCoins, balanceBefore: 0, balanceAfter: startingCoins, itemsTouched: Object.keys(startingInventory), reason: 'Initial giveaway account setup' });
    } else {
      // Fire-and-forget: this username has never been seen before in this
      // process. It's already usable in memory immediately (no need to wait
      // on the DB round-trip before the player can act) - Postgres just
      // needs to catch up with a matching row.
      db.insertNewUser(username, startingCoins, { wagered: 0, won: 0, lost: 0 }).catch((err) => {
        console.error(`[db] insertNewUser failed for ${username}:`, err.message);
      });
    }
  }
  const u = users.get(username);
  if (!u.stats) u.stats = { wagered: 0, won: 0, lost: 0 }; // backfill for accounts created before stats existed
  if (u.specialRole === undefined) u.specialRole = null; // backfill for accounts created before manually-grantable roles existed
  if (u.mutedUntil === undefined) u.mutedUntil = 0; // backfill for accounts created before chat muting existed
  if (isGiveaway && !isNewAccount) {
    // Keep this hand-out account's INVENTORY topped up on every touch (not
    // just at creation) - covers accounts that already existed in memory
    // before this feature was added, and any pets added to the catalog
    // later (they'll get topped up to 99x automatically too). Only the
    // items that actually needed correcting get persisted - once stable at
    // 99x, later calls change nothing and skip the DB write entirely.
    //
    // Coins are deliberately NOT re-floored here anymore (unlike the
    // inventory). They used to be, but that meant an admin's "Remove
    // Coins" action on this account got silently undone within the same
    // request - syncAccount() calls ensureUser() again right after the
    // deduction, which would see the now-lower balance and reset it straight
    // back up before the response even went out. Coins are only ever
    // seeded once now, at creation, same as a normal account - after that
    // they behave like any other balance and admin adjustments actually stick.
    const toppedUp = [];
    for (const id of Object.keys(petCatalog)) {
      if (!u.inventory[id] || u.inventory[id] < 99) { u.inventory[id] = 99; toppedUp.push(id); }
    }
    if (toppedUp.length) {
      persistUser(username, { type: 'giveaway_topup', amount: 0, balanceBefore: u.coins, balanceAfter: u.coins, itemsTouched: toppedUp, reason: 'Self-healing top-up to 99x' });
    }
  }
  return u;
}
function trackWager(username, amount) { if (amount > 0) ensureUser(username).stats.wagered += amount; }
// Resolves a manually-typed username against real, already-known accounts
// case-insensitively - e.g. admin types "dtn_bgsi" but the account is
// actually stored as "DTN_BGSI" (its real Roblox-canonical casing). Used
// anywhere a human free-types someone else's name rather than it coming
// from their own verified login. Returns the real stored key if a match
// exists, otherwise null - callers decide what "no match" means for them
// (admin lookups should say "not found"; tipping may still want to create
// a fresh account for a genuinely new username).
function resolveExistingUsername(raw) {
  const target = String(raw || '').trim();
  if (!target) return null;
  if (users.has(target)) return target;
  const lower = target.toLowerCase();
  for (const key of users.keys()) {
    if (key.toLowerCase() === lower) return key;
  }
  return null;
}
// A cancelled coinflip lobby never actually played out, so it shouldn't
// keep counting toward "Played" / Most Played - this undoes the trackWager
// that ran when the lobby was first created.
function untrackWager(username, amount) { if (amount > 0) { const u = ensureUser(username); u.stats.wagered = Math.max(0, u.stats.wagered - amount); } }
function trackWin(username, amount) { if (amount > 0) ensureUser(username).stats.won += amount; }
function trackLoss(username, amount) { if (amount > 0) ensureUser(username).stats.lost += amount; }

// ---------------------------------------------------------------------------
// Level curve - mirrors the client's exact formula (see wageredForLevel /
// levelForWagered in the frontend) so a player's level, and therefore their
// Rain Pool share, is computed identically on both sides.
// ---------------------------------------------------------------------------
const LEVEL_CURVE_C = 2230808.28;
const LEVEL_CURVE_K = 1.353373;
const MAX_LEVEL = 500;
function levelForWagered(wagered) {
  const w = Math.max(0, wagered || 0);
  if (w <= 0) return 1;
  const lvl = Math.floor(Math.pow(w / LEVEL_CURVE_C, 1 / LEVEL_CURVE_K)) + 1;
  return Math.max(1, Math.min(MAX_LEVEL, lvl));
}

// ---------------------------------------------------------------------------
// Rain Pool - one shared, server-timed pool everyone sees the same countdown
// for (driven by an absolute phaseEndsAt timestamp broadcast to clients, not
// a per-client local timer). Counts down RAIN_COUNTDOWN_MS, then opens a
// RAIN_CLAIM_WINDOW_MS claim window. Clicking "claim" during that window
// doesn't pay out immediately - it just marks you down as a claimant, so the
// button can show "Claimed" until the window closes. When the window closes,
// the pool is split once among everyone who claimed, weighted by level (a
// higher-level player gets a bigger slice), so the total paid out is always
// exactly the pool amount no matter how many people claimed - never one full
// 25k per person.
// ---------------------------------------------------------------------------
const RAIN_BASE = 25000;
const RAIN_COUNTDOWN_MS = 25 * 60 * 1000;
const RAIN_CLAIM_WINDOW_MS = 5 * 60 * 1000;

let rainPool = RAIN_BASE;
let rainPhase = 'counting'; // 'counting' | 'claimable'
let rainPhaseEndsAt = Date.now() + RAIN_COUNTDOWN_MS;
let rainClaimants = new Set(); // usernames who've claimed this cycle, cleared each cycle

function rainPublicState() {
  return { pool: rainPool, phase: rainPhase, phaseEndsAt: rainPhaseEndsAt, claimants: Array.from(rainClaimants) };
}
function broadcastRainState() {
  broadcast({ type: 'rain:state', ...rainPublicState() });
}

function payoutRain() {
  if (rainClaimants.size > 0) {
    const weights = new Map();
    let totalWeight = 0;
    for (const username of rainClaimants) {
      const w = levelForWagered(ensureUser(username).stats.wagered);
      weights.set(username, w);
      totalWeight += w;
    }
    for (const username of rainClaimants) {
      const share = Math.floor(rainPool * (weights.get(username) / totalWeight));
      if (share > 0) {
        const u = ensureUser(username);
        const before = u.coins;
        u.coins += share;
        persistUser(username, { type: 'rain_payout', amount: share, balanceBefore: before, balanceAfter: u.coins });
        syncAccount(username);
        send(usernameToSocket.get(username), { type: 'rain:payout', amount: share });
      }
    }
  }
  rainPool = RAIN_BASE;
  rainPhase = 'counting';
  rainPhaseEndsAt = Date.now() + RAIN_COUNTDOWN_MS;
  rainClaimants = new Set();
  broadcastRainState();
}

function handleRainDeposit(username, msg) {
  const amount = Math.floor(Number(msg.amount));
  if (!amount || amount < 1) return;
  const u = ensureUser(username);
  if (u.coins < amount) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't have enough coins for that." });
  }
  const before = u.coins;
  u.coins -= amount;
  rainPool += amount;
  persistUser(username, { type: 'rain_deposit', amount: -amount, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  broadcastRainState();
}

function handleRainClaim(username) {
  if (rainPhase !== 'claimable') return;
  if (rainClaimants.has(username)) return; // already claimed this cycle
  rainClaimants.add(username);
  broadcastRainState(); // lets every client (including this one) know it's claimed
}

setInterval(() => {
  const now = Date.now();
  if (now < rainPhaseEndsAt) return;
  if (rainPhase === 'counting') {
    rainPhase = 'claimable';
    rainPhaseEndsAt = now + RAIN_CLAIM_WINDOW_MS;
    rainClaimants = new Set();
    broadcastRainState();
  } else {
    payoutRain();
  }
}, 1000);

function itemValue(id) {
  const p = petCatalog[id];
  return p ? p.value : 0;
}
function stakeValue(items) {
  return items.reduce((sum, id) => sum + itemValue(id), 0);
}

// Finds the subset of `items` (with at most `maxItems` items in it) whose
// combined value is closest to `target`. Used to pick out exactly which
// item(s) make up the "excess" on the larger side of an uneven-but-within-
// range coinflip stake, so that excess can be carved out as the house rake
// while the rest flips normally.
// Exhaustive search - fine since a single stake realistically has a small
// handful of items (2^n), but capped defensively just in case. The item
// cap is enforced WHILE searching (only subsets of size <= maxItems are
// ever considered), not as an after-the-fact filter - otherwise the search
// happily finds some large, far-better-fitting combination and then the
// caller has to throw the whole thing away for being too big, which is
// exactly what was happening before this fix.
function pickClosestSubset(items, target, maxItems){
  if(!items.length || target <= 0) return [];
  const n = Math.min(items.length, 20);
  const cap = maxItems && maxItems > 0 ? Math.min(maxItems, n) : n;
  const withValues = items.slice(0, n).map(id => ({ id, value: itemValue(id) }));
  let best = [], bestDiff = Infinity;
  for(let mask = 1; mask < (1 << n); mask++){
    let sum = 0; let count = 0; const subset = [];
    for(let i = 0; i < n; i++) if(mask & (1 << i)){ sum += withValues[i].value; subset.push(withValues[i].id); count++; }
    if(count > cap) continue; // respect the item-count cap during the search, not after
    const diff = Math.abs(sum - target);
    if(diff < bestDiff){ bestDiff = diff; best = subset; }
  }
  return best;
}
function ownsAll(username, items) {
  const inv = ensureUser(username).inventory;
  const locked = lockedItemsForUser(username);
  const need = {};
  for (const id of items) need[id] = (need[id] || 0) + 1;
  return Object.entries(need).every(([id, qty]) => ((inv[id] || 0) - (locked[id] || 0)) >= qty);
}
// Items sitting inside a player's own PENDING withdrawal request(s) are
// "locked" - still physically in their inventory (nothing is actually
// removed until an admin fulfills the request), but unavailable for
// wagering, staking, or a second withdrawal request, so a player can't
// submit a withdrawal and then gamble the same pets away before the admin
// gets to it. Unlocks automatically the moment the request resolves
// (fulfilled/rejected/cancelled), since this is just derived from whatever
// is still 'pending' right now - no separate unlock bookkeeping needed.
function lockedItemsForUser(username) {
  const locked = {};
  for (const req of withdrawRequests) {
    if (req.username !== username || req.status !== 'pending') continue;
    for (const id of req.items) locked[id] = (locked[id] || 0) + 1;
  }
  return locked;
}
function removeItems(username, items) {
  const inv = ensureUser(username).inventory;
  for (const id of items) inv[id] = (inv[id] || 0) - 1;
}
function addItems(username, items) {
  const inv = ensureUser(username).inventory;
  for (const id of items) inv[id] = (inv[id] || 0) + 1;
}

function send(ws, msg) {
  if (ws && ws.readyState === ws.OPEN) ws.send(JSON.stringify(msg));
}
function broadcast(msg) {
  const data = JSON.stringify(msg);
  for (const ws of wss.clients) {
    if (ws.readyState === ws.OPEN) ws.send(data);
  }
}

// ---------------------------------------------------------------------------
// Live feed - a rolling site-wide log of the last FEED_MAX things that just
// happened across every game (Coinflip, Case Battles, Jackpot, Mines,
// Cases), so the home page can show real activity instead of just your own.
// Kept in memory only (not persisted) - a fresh server restart just starts
// the feed empty again, which is fine for something this ephemeral.
// ---------------------------------------------------------------------------
const FEED_MAX = 10;
let liveFeed = []; // newest first

function pushFeedEvent(entry) {
  const full = { id: 'feed_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8), at: Date.now(), ...entry };
  liveFeed.unshift(full);
  if (liveFeed.length > FEED_MAX) liveFeed.length = FEED_MAX;
  broadcast({ type: 'feed:event', entry: full });
}

// Chat history - purely in-memory (resets on restart, same as the rest of
// this file's live state), but at least survives a client-side page
// refresh now: previously the chat log was rebuilt ONLY from live
// chat:message broadcasts received while connected, so refreshing (or
// reconnecting) wiped it back to completely empty even though the
// conversation was still very much ongoing for everyone else. Kept oldest-
// first (chronological), capped at CHAT_HISTORY_MAX - once full, the
// oldest message drops off the front to make room, same "1st one
// disappears" behavior the client's own CHAT_MAX_MESSAGES cap already had.
const CHAT_HISTORY_MAX = 100;
let chatHistory = [];

function pushChatMessage(entry) {
  chatHistory.push(entry);
  if (chatHistory.length > CHAT_HISTORY_MAX) chatHistory.shift();
  broadcast({ type: 'chat:message', ...entry });
}

function syncAccount(username) {
  const ws = usernameToSocket.get(username);
  if (!ws) return; // not currently connected - they'll get fresh state on next login
  const u = ensureUser(username);
  const myPendingWithdrawals = withdrawRequests
    .filter((r) => r.username === username && r.status === 'pending')
    .map((r) => ({ id: r.id, items: r.items, requestedAt: r.requestedAt }));
  send(ws, {
    type: 'account',
    user: {
      username, coins: u.coins, inventory: u.inventory, stats: u.stats,
      specialRole: u.specialRole || null, mutedUntil: u.mutedUntil || 0,
      lockedItems: lockedItemsForUser(username),
      pendingWithdrawals: myPendingWithdrawals,
    },
  });
}

// Fire-and-forget persistence: memory has already been updated synchronously
// (same as before this feature existed) by the time this is called, so this
// just mirrors that already-decided state into Postgres afterward. Errors
// are logged, not thrown - a slow/hiccupping DB write should never crash a
// live game round or block the response the player already got.
//
// `txn` (optional) - see db.js's persistUserState doc comment for shape.
// Pass it whenever coins or stats changed, so a real audit row gets written.
function persistUser(username, txn) {
  const u = users.get(username);
  if (!u) return;
  db.persistUserState(username, u, txn).catch((err) => {
    console.error(`[db] persistUser failed for ${username} (${txn ? txn.type : 'no-txn'}):`, err.message);
  });
}

// ---------------------------------------------------------------------------
// Shared game math (mirrors the client's weightedPick/getPool exactly)
// ---------------------------------------------------------------------------
function weightedPick(pool) {
  const total = pool.reduce((s, it) => s + it.chance, 0);
  let roll = Math.random() * total;
  for (const it of pool) {
    roll -= it.chance;
    if (roll <= 0) return it;
  }
  return pool[pool.length - 1];
}
function getPool(caseIndex) {
  const items = caseItems[caseIndex];
  if (items && items.length) return items;
  const c = caseData[caseIndex];
  return [{ name: 'Mystery Prize', value: c.price, chance: 100 }];
}
function pickBotNames(n, pool) {
  const shuffled = pool.slice().sort(() => Math.random() - 0.5);
  return shuffled.slice(0, n);
}

// ---------------------------------------------------------------------------
// Coinflip
// ---------------------------------------------------------------------------
let cfLobbies = []; // { id, creator, side, items }

function broadcastCfLobbies() {
  broadcast({ type: 'coinflip:lobbies', lobbies: cfLobbies.map((l) => ({ id: l.id, creator: l.creator, side: l.side, items: l.items })) });
}


// Rake target: 7.5% of the TOTAL pot value, taken from the winner's full
// haul AFTER the flip resolves (not carved from either side beforehand).
// Since items are discrete, the actual amount taken will land near 7.5% but
// not exactly on it - CF_RAKE_MAX_MULTIPLE caps how far over that's allowed
// to drift; if nothing in the winner's haul comes reasonably close without
// blowing way past the target (e.g. the only candidate is one huge pet),
// no rake is taken at all rather than grabbing something oversized.
// Perfectly even 1-for-1 stakes (both sides worth exactly the same) are
// exempt from the rake entirely, regardless of the above.
const CF_RAKE_TARGET_PCT = 0.075;
const CF_RAKE_MAX_MULTIPLE = 1.5; // never take more than ~1.5x target (~11.25% of pot) - skip entirely past that
const CF_RAKE_MAX_ITEMS = 2; // hard cap: never take more than 2 individual items as rake, no matter what the value math says

function subtractItemList(full, toRemove){
  const remaining = [...full];
  for(const id of toRemove){
    const idx = remaining.indexOf(id);
    if(idx !== -1) remaining.splice(idx, 1);
  }
  return remaining;
}

function resolveCoinflip(creator, creatorSide, creatorItems, joiner, joinerSide, joinerItems) {
  const result = Math.random() < 0.5 ? 'H' : 'T';
  const winner = result === creatorSide ? creator : joiner;
  const loser = winner === creator ? joiner : creator;
  const winnerOwnItems = winner === creator ? creatorItems : joinerItems;
  const loserItems = winner === creator ? joinerItems : creatorItems;
  const fullHaul = [...winnerOwnItems, ...loserItems]; // winner's own stake back + everything the loser staked

  const creatorValue = stakeValue(creatorItems);
  const joinerValue = stakeValue(joinerItems);
  const totalPotValue = creatorValue + joinerValue;
  const targetRake = totalPotValue * CF_RAKE_TARGET_PCT;
  let rakeItems = [];
  // Perfectly even 1-for-1 stakes (both sides worth exactly the same) are
  // exempt from the rake entirely - only imbalanced-or-uneven pots get raked.
  if (creatorValue !== joinerValue && targetRake > 0 && fullHaul.length > 0) {
    const candidate = pickClosestSubset(fullHaul, targetRake, CF_RAKE_MAX_ITEMS);
    const candidateValue = stakeValue(candidate);
    // Two independent safety limits, both must pass: the value can't drift
    // too far past the target (CF_RAKE_MAX_MULTIPLE), AND the item COUNT is
    // hard-capped (CF_RAKE_MAX_ITEMS) regardless of value - so even if the
    // value-matching logic ever picks a surprising combination, it physically
    // cannot take more than a couple of items no matter what.
    if (candidateValue > 0 && candidate.length <= CF_RAKE_MAX_ITEMS && candidateValue <= targetRake * CF_RAKE_MAX_MULTIPLE) {
      rakeItems = candidate;
    }
    console.log(`[cf-rake] pot=${totalPotValue} target=${Math.round(targetRake)} candidate=${JSON.stringify(candidate)} candidateValue=${candidateValue} candidateCount=${candidate.length} taken=${JSON.stringify(rakeItems)}`);
  }
  const winnerFinalItems = rakeItems.length ? subtractItemList(fullHaul, rakeItems) : fullHaul;

  // Both sides are always real players now - bots never participate in
  // Coinflip anymore, so this always tracks stats/persists for both.
  const wonAmount = stakeValue(loserItems);
  addItems(winner, winnerFinalItems);
  trackWin(winner, wonAmount);
  persistUser(winner, { type: 'coinflip_win', amount: 0, itemsTouched: [...new Set(winnerFinalItems)] });
  trackLoss(loser, wonAmount);
  persistUser(loser, { type: 'coinflip_loss', amount: 0 });
  if (rakeItems.length) {
    addItems(ADMIN_USERNAME, rakeItems);
    persistUser(ADMIN_USERNAME, { type: 'coinflip_rake', amount: 0, itemsTouched: [...new Set(rakeItems)] });
    syncAccount(ADMIN_USERNAME);
  }

  syncAccount(creator);
  syncAccount(joiner);
  broadcast({ type: 'coinflip:result', creator, creatorSide, creatorItems, joiner, joinerSide, joinerItems, winner, result });
  pushFeedEvent({ game: 'coinflip', username: winner, amount: wonAmount });
  db.insertCoinflipHistory({ creator, joiner, creatorSide, joinerSide, creatorItems, joinerItems, creatorValue, joinerValue, result, winner }).catch((err) => {
    console.error('[db] Failed to persist coinflip history:', err.message);
  });

  broadcastCfLobbies();
}

function handleCoinflipCreate(username, msg) {
  const items = msg.items || [];
  if (!items.length || !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }
  removeItems(username, items); // escrow
  trackWager(username, stakeValue(items));
  persistUser(username, { type: 'coinflip_create_escrow', amount: 0, itemsTouched: [...new Set(items)] });
  const id = 'cf_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8);
  const lobby = { id, creator: username, side: msg.side, items };
  cfLobbies.push(lobby);
  // Persisted so a server restart while this lobby is still waiting for an
  // opponent doesn't lose track of it - the items were already escrowed out
  // of the creator's inventory above (see removeItems), and without this
  // the lobby (the only record of who those items belong to) would simply
  // vanish from memory on restart with no way to ever return them.
  db.insertCoinflipLobby(lobby).catch((err) => {
    console.error(`[db] Failed to persist coinflip lobby ${id}:`, err.message);
  });
  syncAccount(username);
  broadcastCfLobbies();
  // The lobby just sits here now, waiting for a real player to join via
  // handleCoinflipJoin below - no automatic bot opponent gets spawned for
  // it anymore, no matter how long it waits.
}

function handleCoinflipJoin(username, msg) {
  const lobby = cfLobbies.find((l) => l.id === msg.lobbyId);
  if (!lobby) return send(usernameToSocket.get(username), { type: 'error', message: 'That lobby is no longer available.' });
  const items = msg.items || [];
  if (!items.length || !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }
  const lobbyValue = stakeValue(lobby.items);
  const joinValue = stakeValue(items);
  const lo = lobbyValue * (1 - CF_MATCH_TOLERANCE), hi = lobbyValue * (1 + CF_MATCH_TOLERANCE);
  if (joinValue < lo || joinValue > hi) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'Your stake is outside the allowed ±10% range.' });
  }
  removeItems(username, items); // escrow
  trackWager(username, joinValue);
  persistUser(username, { type: 'coinflip_join_escrow', amount: 0, itemsTouched: [...new Set(items)] });
  cfLobbies = cfLobbies.filter((l) => l.id !== msg.lobbyId);
  db.deleteCoinflipLobby(msg.lobbyId).catch((err) => {
    console.error(`[db] Failed to delete resolved coinflip lobby ${msg.lobbyId}:`, err.message);
  });
  broadcastCfLobbies();
  const joinerSide = lobby.side === 'H' ? 'T' : 'H';
  resolveCoinflip(lobby.creator, lobby.side, lobby.items, username, joinerSide, items);
}

function handleCoinflipCancel(username, msg) {
  const lobby = cfLobbies.find((l) => l.id === msg.lobbyId);
  if (!lobby || lobby.creator !== username) return;
  addItems(username, lobby.items); // return escrow
  untrackWager(username, stakeValue(lobby.items)); // never actually played - shouldn't count as "played"
  persistUser(username, { type: 'coinflip_cancel_refund', amount: 0, itemsTouched: [...new Set(lobby.items)] });
  cfLobbies = cfLobbies.filter((l) => l.id !== msg.lobbyId);
  db.deleteCoinflipLobby(msg.lobbyId).catch((err) => {
    console.error(`[db] Failed to delete cancelled coinflip lobby ${msg.lobbyId}:`, err.message);
  });
  syncAccount(username);
  broadcastCfLobbies();
}

// ---------------------------------------------------------------------------
// Dice Duel - 1v1, same escrow/ownership/±10%-match/7.5%-rake patterns as
// Coinflip above (reusing ownsAll/removeItems/addItems/stakeValue/
// pickClosestSubset/subtractItemList/CF_RAKE_* directly rather than
// duplicating that logic), but unlike Coinflip this doesn't resolve
// instantly on join - it keeps rolling a die every ROLL_PACE_MS until it
// lands on either player's chosen number, so a duel is a small live "battle"
// (much closer in shape to Case Battles' multi-round runBattle() than to
// Coinflip's single synchronous flip). Each duel lives in `diceDuels` for
// its whole lifecycle (waiting -> running -> finished) and the full list is
// broadcast on every change, the same way casebattle:list works - so late
// joiners/spectators can see an in-progress duel's roll history, not just
// open lobbies waiting for a second player.
// ---------------------------------------------------------------------------
const DICE_DUEL_ROLL_PACE_MS = 1100;
const DICE_DUEL_FINISHED_DISPLAY_MS = 12000;
let diceDuels = new Map(); // id -> duel

function diceDuelPublicList() {
  return [...diceDuels.values()].map((d) => ({
    id: d.id, status: d.status,
    creator: d.creator, creatorItems: d.creatorItems, creatorValue: d.creatorValue, creatorNumber: d.creatorNumber,
    joiner: d.joiner || null, joinerItems: d.joinerItems || [], joinerValue: d.joinerValue || 0, joinerNumber: d.joinerNumber || null,
    rolls: d.rolls, winner: d.winner || null, winnerValue: d.winnerValue || 0,
  }));
}
function broadcastDiceDuels() {
  broadcast({ type: 'diceduel:list', duels: diceDuelPublicList() });
}

function isValidDiceNumber(n) {
  return Number.isInteger(n) && n >= 1 && n <= 6;
}

function handleDiceDuelCreate(username, msg) {
  const items = msg.items || [];
  const number = Number(msg.number);
  if (!items.length || !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }
  if (!isValidDiceNumber(number)) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'Pick a number from 1 to 6.' });
  }
  removeItems(username, items); // escrow
  const creatorValue = stakeValue(items);
  trackWager(username, creatorValue);
  persistUser(username, { type: 'diceduel_create_escrow', amount: 0, itemsTouched: [...new Set(items)] });
  const id = 'dd_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8);
  diceDuels.set(id, {
    id, status: 'waiting',
    creator: username, creatorItems: items, creatorValue, creatorNumber: number,
    joiner: null, joinerItems: [], joinerValue: 0, joinerNumber: null,
    rolls: [], winner: null, winnerValue: 0,
  });
  syncAccount(username);
  broadcastDiceDuels();
}

function handleDiceDuelJoin(username, msg) {
  const duel = diceDuels.get(msg.duelId);
  if (!duel || duel.status !== 'waiting') {
    return send(usernameToSocket.get(username), { type: 'error', message: 'That duel is no longer available.' });
  }
  if (duel.creator === username) return; // can't join your own duel
  const items = msg.items || [];
  const number = Number(msg.number);
  if (!items.length || !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }
  if (!isValidDiceNumber(number)) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'Pick a number from 1 to 6.' });
  }
  // Never trust the client to grey out the creator's number client-side only
  // - re-checked here regardless of what the join request claims.
  if (number === duel.creatorNumber) {
    return send(usernameToSocket.get(username), { type: 'error', message: `${duel.creatorNumber} is already taken - pick a different number.` });
  }
  const joinValue = stakeValue(items);
  const lo = duel.creatorValue * (1 - CF_MATCH_TOLERANCE), hi = duel.creatorValue * (1 + CF_MATCH_TOLERANCE);
  if (joinValue < lo || joinValue > hi) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'Your stake is outside the allowed ±10% range.' });
  }

  removeItems(username, items); // escrow
  trackWager(username, joinValue);
  persistUser(username, { type: 'diceduel_join_escrow', amount: 0, itemsTouched: [...new Set(items)] });

  duel.status = 'running';
  duel.joiner = username;
  duel.joinerItems = items;
  duel.joinerValue = joinValue;
  duel.joinerNumber = number;
  syncAccount(username);
  broadcastDiceDuels();
  runDiceDuelRolls(duel.id);
}

function handleDiceDuelCancel(username, msg) {
  const duel = diceDuels.get(msg.duelId);
  if (!duel || duel.creator !== username || duel.status !== 'waiting') return;
  cancelDiceDuelInternal(duel);
}

// Shared refund/cleanup, used both by an explicit cancel request and by the
// disconnect handler below - a duel only ever gets refunded this one way,
// so there's a single place that can return the escrow exactly once.
function cancelDiceDuelInternal(duel) {
  addItems(duel.creator, duel.creatorItems); // return escrow
  untrackWager(duel.creator, duel.creatorValue); // never actually played - shouldn't count as "played"
  persistUser(duel.creator, { type: 'diceduel_cancel_refund', amount: 0, itemsTouched: [...new Set(duel.creatorItems)] });
  diceDuels.delete(duel.id);
  syncAccount(duel.creator);
  broadcastDiceDuels();
}

async function runDiceDuelRolls(duelId) {
  const duel = diceDuels.get(duelId);
  if (!duel) return;
  while (true) {
    const current = diceDuels.get(duelId);
    if (!current || current.status !== 'running') return; // duel vanished/already resolved - stop
    const result = 1 + Math.floor(Math.random() * 6); // server-generated; the client only ever receives this and animates it
    current.rolls.push(result);
    broadcast({ type: 'diceduel:roll', duelId, result, rollIdx: current.rolls.length - 1 });
    if (result === current.creatorNumber || result === current.joinerNumber) {
      resolveDiceDuel(current, result);
      return;
    }
    await new Promise((r) => setTimeout(r, DICE_DUEL_ROLL_PACE_MS));
  }
}

// Parallels resolveCoinflip's payout/rake logic (same CF_RAKE_* constants,
// same pickClosestSubset/subtractItemList helpers) without touching
// resolveCoinflip itself - Coinflip's own behavior stays exactly as it was.
function resolveDiceDuel(duel, finalRoll) {
  const winner = finalRoll === duel.creatorNumber ? duel.creator : duel.joiner;
  const loser = winner === duel.creator ? duel.joiner : duel.creator;
  const winnerOwnItems = winner === duel.creator ? duel.creatorItems : duel.joinerItems;
  const loserItems = winner === duel.creator ? duel.joinerItems : duel.creatorItems;
  const fullHaul = [...winnerOwnItems, ...loserItems];

  const totalPotValue = duel.creatorValue + duel.joinerValue;
  const targetRake = totalPotValue * CF_RAKE_TARGET_PCT;
  let rakeItems = [];
  if (duel.creatorValue !== duel.joinerValue && targetRake > 0 && fullHaul.length > 0) {
    const candidate = pickClosestSubset(fullHaul, targetRake, CF_RAKE_MAX_ITEMS);
    const candidateValue = stakeValue(candidate);
    if (candidateValue > 0 && candidate.length <= CF_RAKE_MAX_ITEMS && candidateValue <= targetRake * CF_RAKE_MAX_MULTIPLE) {
      rakeItems = candidate;
    }
  }
  const winnerFinalItems = rakeItems.length ? subtractItemList(fullHaul, rakeItems) : fullHaul;

  const wonAmount = stakeValue(loserItems);
  addItems(winner, winnerFinalItems);
  trackWin(winner, wonAmount);
  persistUser(winner, { type: 'diceduel_win', amount: 0, itemsTouched: [...new Set(winnerFinalItems)] });
  trackLoss(loser, wonAmount);
  persistUser(loser, { type: 'diceduel_loss', amount: 0 });
  if (rakeItems.length) {
    addItems(ADMIN_USERNAME, rakeItems);
    persistUser(ADMIN_USERNAME, { type: 'diceduel_rake', amount: 0, itemsTouched: [...new Set(rakeItems)] });
    syncAccount(ADMIN_USERNAME);
  }

  syncAccount(duel.creator);
  syncAccount(duel.joiner);

  duel.status = 'finished';
  duel.winner = winner;
  duel.winnerValue = totalPotValue - stakeValue(rakeItems);
  broadcast({ type: 'diceduel:finished', duelId: duel.id, winner, winnerValue: duel.winnerValue, rolls: duel.rolls });
  pushFeedEvent({ game: 'diceduel', username: winner, amount: wonAmount });
  broadcastDiceDuels();

  // Same lifecycle as a finished Case Battle - stay visible briefly, then
  // drop out of the shared list so it doesn't pile up forever.
  // The client doesn't reveal "X won" in the shared lobby list until it's
  // paced through every one of this duel's rolls at ~6s each, matching the
  // battle modal's own animation pace (see DD_ROLL_MS client-side). With a
  // flat 12s window here, any duel with more than 2 rolls - which is most
  // of them, since it typically takes ~3 rolls for either number to hit -
  // got pruned from the list before the client's own delay ever elapsed.
  // The row would just vanish, having never actually shown the winner.
  // Scale this duel's window to its own roll count instead, with enough
  // buffer afterward to actually see the result before it clears out.
  const revealDelayMs = duel.rolls.length * 6000;
  const displayMs = Math.max(DICE_DUEL_FINISHED_DISPLAY_MS, revealDelayMs + 8000);
  setTimeout(() => {
    const stillThere = diceDuels.get(duel.id);
    if (stillThere && stillThere.status === 'finished') {
      diceDuels.delete(duel.id);
      broadcastDiceDuels();
    }
  }, displayMs);
}

// ---------------------------------------------------------------------------
// Jackpot - one shared round site-wide (not per-lobby): everyone who enters
// within the 60s window throws coins and/or items into the same pot, and a
// single weighted-random winner takes it all. This used to be simulated
// entirely client-side with fake bots, which is why two real players never
// saw each other's entries - now the round itself lives here, and every
// connected client just renders whatever state gets broadcast to it.
// ---------------------------------------------------------------------------
const JACKPOT_ROUND_MS = 60 * 1000;
const JACKPOT_MIN_ENTRANTS = 2; // a round must not resolve/pay out with only one participant
let jackpotRound = null; // { entrants: [{username, value, items, coinsStaked}], endsAt, timer }

function jackpotPublicState() {
  if (!jackpotRound) return { open: false, entrants: [], endsAt: 0 };
  return {
    open: true,
    endsAt: jackpotRound.endsAt,
    entrants: jackpotRound.entrants.map((e) => ({ username: e.username, value: e.value, items: e.items })),
  };
}
function broadcastJackpot() {
  broadcast({ type: 'jackpot:state', ...jackpotPublicState() });
}

function handleJackpotEnter(username, msg) {
  const amount = Math.max(0, Math.floor(Number(msg.amount) || 0));
  const items = Array.isArray(msg.items) ? msg.items.filter((id) => typeof id === 'string') : [];
  if (amount <= 0 && items.length === 0) return;

  if (jackpotRound && jackpotRound.entrants.some((e) => e.username === username)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You've already entered this round." });
  }

  const u = ensureUser(username);
  if (amount > 0 && amount > u.coins) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'Not enough coins.' });
  }
  if (items.length && !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }

  if (amount > 0) u.coins -= amount;
  if (items.length) removeItems(username, items); // escrow
  const value = amount + stakeValue(items);
  trackWager(username, value);
  persistUser(username, { type: 'jackpot_enter', amount: -amount, itemsTouched: [...new Set(items)] });
  syncAccount(username);

  if (!jackpotRound) {
    // The round exists as soon as the first person's in it, but the
    // countdown itself does NOT start yet (endsAt stays 0 / no timer
    // scheduled) - a lone entrant just waits indefinitely with the clock
    // frozen instead of watching a countdown tick toward a resolution that
    // can't actually happen yet with only one participant.
    jackpotRound = { entrants: [], endsAt: 0, timer: null };
  }
  jackpotRound.entrants.push({ username, value, items, coinsStaked: amount });

  if (jackpotRound.entrants.length >= JACKPOT_MIN_ENTRANTS && !jackpotRound.timer) {
    // The 2nd entrant just joined - only now does the real countdown begin,
    // and it's the same endsAt broadcast to every client, so everyone sees
    // an identical clock rather than each client running its own timer.
    jackpotRound.endsAt = Date.now() + JACKPOT_ROUND_MS;
    jackpotRound.timer = setTimeout(resolveJackpot, JACKPOT_ROUND_MS);
  }
  broadcastJackpot();
}

function resolveJackpot() {
  const round = jackpotRound;
  if (!round || round.entrants.length === 0) { jackpotRound = null; broadcastJackpot(); return; }
  if (round.entrants.length < JACKPOT_MIN_ENTRANTS) {
    // Shouldn't happen now that the timer is only ever scheduled once a 2nd
    // entrant joins (see handleJackpotEnter) - kept as a defensive fallback
    // in case that invariant is ever broken by a future change. Re-freezes
    // the clock rather than resolving/discarding a lone entrant's stake.
    round.endsAt = 0;
    round.timer = null;
    broadcastJackpot();
    return;
  }
  jackpotRound = null;

  const total = round.entrants.reduce((s, e) => s + e.value, 0);
  let r = Math.random() * total;
  let winner = round.entrants[round.entrants.length - 1];
  let cum = 0;
  for (const e of round.entrants) { cum += e.value; if (r <= cum) { winner = e; break; } }

  const coinsPortion = round.entrants.reduce((s, e) => s + e.coinsStaked, 0);
  const allItems = round.entrants.reduce((arr, e) => arr.concat(e.items), []);
  const u = ensureUser(winner.username);
  const before = u.coins;
  if (coinsPortion > 0) u.coins += coinsPortion;
  if (allItems.length) addItems(winner.username, allItems);
  trackWin(winner.username, total);
  persistUser(winner.username, { type: 'jackpot_win', amount: coinsPortion, balanceBefore: before, balanceAfter: u.coins, itemsTouched: [...new Set(allItems)] });
  for (const e of round.entrants) {
    if (e.username !== winner.username) {
      trackLoss(e.username, e.value);
      persistUser(e.username, { type: 'jackpot_loss', amount: 0 });
    }
  }
  // trackLoss above only touches the server's copy of each loser's stats -
  // without syncing them individually too, only the winner's own client
  // ever finds out anything happened, so everyone else's Profile tab (and
  // their own contribution to the leaderboard) just sits stale forever.
  for (const e of round.entrants) syncAccount(e.username);

  broadcast({
    type: 'jackpot:result',
    winner: winner.username,
    total,
    entrants: round.entrants.map((e) => ({ username: e.username, value: e.value })),
  });
  pushFeedEvent({ game: 'jackpot', username: winner.username, amount: total });
  broadcastJackpot();
}

// ---------------------------------------------------------------------------
// Case Battles
// ---------------------------------------------------------------------------
const battles = new Map(); // id -> battle

// Crazy/Jackpot/Terminal are winner-selection modifiers layered on top of the
// existing FFA/Team configs - not new modeConfigs entries. The client already
// simulates all three offline (mockRunBattle) for when it's disconnected from
// the server; runBattle() below mirrors that exact math so the animation the
// player already tested against matches the real, server-authoritative result.
const WIN_MODES = new Set(['normal', 'crazy', 'jackpot', 'terminal']);

function battleCost(caseQueue) {
  return caseQueue.reduce((sum, idx) => sum + caseData[idx].price, 0);
}
// Picks a team for a new auto-assigned player (a bot, or a join that didn't
// request a specific side) based on ACTUAL current occupancy - never blind
// alternation. Team choice (see handleCaseBattleJoin) means a team can fill
// up "out of turn" relative to simple join order, so anything that used to
// assume team === players.length % 2 could end up assigning into an
// already-full team once that happened - this is what actually caused a
// 3-vs-1 battle after a manually-chosen join left the teams uneven partway
// through. Always fills whichever team genuinely has room, preferring the
// less-filled side when both do.
function pickAutoTeam(b) {
  if (!b.cfg.isTeam) return 0;
  const teamSize = b.cfg.teamSize || Math.floor(b.cfg.count / 2);
  const teamACount = b.players.filter((p) => p.team === 0).length;
  const teamBCount = b.players.filter((p) => p.team === 1).length;
  if (teamACount < teamSize && teamACount <= teamBCount) return 0;
  if (teamBCount < teamSize) return 1;
  return 0; // both full - shouldn't be reachable since callers already check b.players.length < b.cfg.count first
}
function broadcastBattles() {
  broadcast({
    type: 'casebattle:list',
    battles: [...battles.values()].map((b) => ({
      id: b.id, creator: b.creator, status: b.status, mode: b.mode, winMode: b.winMode,
      caseQueue: b.caseQueue, caseNames: b.caseNames,
      players: b.players.map((p) => ({ username: p.username, isBot: p.isBot, team: p.team, total: p.total || 0 })),
      winner: b.winner, winnerValue: b.winnerValue,
    })),
  });
}

function handleCaseBattleCreate(username, msg) {
  const cfg = modeConfigs[msg.mode] || modeConfigs['ffa-2'];
  const winMode = WIN_MODES.has(msg.winMode) ? msg.winMode : 'normal';
  const cost = battleCost(msg.caseQueue);
  const u = ensureUser(username);
  if (u.coins < cost) return send(usernameToSocket.get(username), { type: 'error', message: "You don't have enough coins for this battle." });
  const before = u.coins;
  u.coins -= cost;
  trackWager(username, cost);
  persistUser(username, { type: 'casebattle_create_wager', amount: -cost, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);

  const id = 'battle_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8);
  const caseNames = msg.caseQueue.map((i) => caseData[i].name);
  battles.set(id, {
    id, creator: username, status: 'waiting', mode: msg.mode, winMode,
    caseQueue: msg.caseQueue, caseNames, cfg,
    players: [{ username, isBot: false, team: 0, total: 0, lastPull: 0 }],
  });
  broadcastBattles();

  // Waiting is now player-driven (the creator clicks "Call Bots" whenever
  // they want, or waits for a real join) rather than a fixed countdown. This
  // is just a cleanup safety net for a battle that got truly abandoned -
  // e.g. the creator closed the tab and never came back.
  setTimeout(() => {
    const b = battles.get(id);
    if (b && b.status === 'waiting') startBattle(b);
  }, CASEBATTLE_ABANDON_MS);
}

function handleCaseBattleJoin(username, msg) {
  const b = battles.get(msg.battleId);
  if (!b || b.status !== 'waiting' || b.players.length >= b.cfg.count) {
    return send(usernameToSocket.get(username), { type: 'error', message: 'That battle already started or is full.' });
  }
  const cost = battleCost(b.caseQueue);
  const u = ensureUser(username);
  if (u.coins < cost) return send(usernameToSocket.get(username), { type: 'error', message: "You don't have enough coins for this battle." });

  // The joining player can request which team to sit on - never trusted
  // blindly: it's only honored if it's actually a valid team index for this
  // battle's config AND that team still has room, exactly the same capacity
  // check that already governs the automatic/fallback assignment below.
  // Anything invalid (missing, out of range, or a full team) just falls
  // back to the original alternating auto-assignment, same as before this
  // feature existed.
  let team = pickAutoTeam(b);
  if (b.cfg.isTeam && msg.team !== undefined) {
    const requested = Number(msg.team);
    const teamCount = b.cfg.teamSize || Math.floor(b.cfg.count / 2);
    if (Number.isInteger(requested) && requested >= 0 && requested < 2) {
      const currentOnTeam = b.players.filter((p) => p.team === requested).length;
      if (currentOnTeam < teamCount) {
        team = requested;
      } else {
        return send(usernameToSocket.get(username), { type: 'error', message: 'That team is already full.' });
      }
    }
  }

  const before = u.coins;
  u.coins -= cost;
  trackWager(username, cost);
  persistUser(username, { type: 'casebattle_join_wager', amount: -cost, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);

  b.players.push({ username, isBot: false, team, total: 0, lastPull: 0 });
  broadcastBattles();

  if (b.players.length >= b.cfg.count) startBattle(b); // filled up early - start right away
}

function handleCaseBattleStart(username, msg) {
  const b = battles.get(msg.battleId);
  if (!b || b.status !== 'waiting' || b.creator !== username) return; // only the creator can force-start their own battle early
  startBattle(b);
}

// Fills exactly ONE empty seat with a bot (rather than the whole battle at
// once) so the waiting room can show per-seat "Call Bot" buttons, matching
// how real joins fill seats one at a time. Auto-starts once every seat is
// full, same as a real join filling the last spot.
function handleCaseBattleCallBot(username, msg) {
  const b = battles.get(msg.battleId);
  if (!b || b.status !== 'waiting' || b.creator !== username) return;
  if (b.players.length >= b.cfg.count) return;
  const usedNames = new Set(b.players.filter((p) => p.isBot).map((p) => p.username));
  const availablePool = botNamesBattles.filter((n) => !usedNames.has(n));
  const bots = pickBotNames(1, availablePool.length ? availablePool : botNamesBattles);
  const team = pickAutoTeam(b);
  b.players.push({ username: bots[0], isBot: true, team, total: 0, lastPull: 0 });
  broadcastBattles();
  if (b.players.length >= b.cfg.count) startBattle(b);
}

// Lets the creator back out of their own battle before anyone/anything else
// has taken a seat - refunds their case cost and removes the battle. Once
// ANYONE else has a seat (a real player who has already staked their own
// coins, OR a bot the creator called in themselves), cancelling is blocked -
// previously only a real player joining blocked it, so a creator who called
// in even one bot could still cancel and effectively undo that bot seat,
// which is no longer allowed.
function handleCaseBattleCancel(username, msg) {
  const b = battles.get(msg.battleId);
  if (!b || b.creator !== username || b.status !== 'waiting') return;
  const anyoneElseJoined = b.players.length > 1;
  if (anyoneElseJoined) return;
  const cost = battleCost(b.caseQueue);
  const u = ensureUser(username);
  const before = u.coins;
  u.coins += cost;
  untrackWager(username, cost);
  persistUser(username, { type: 'casebattle_cancel_refund', amount: cost, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  battles.delete(b.id);
  broadcastBattles();
}

function startBattle(b) {
  if (b.status !== 'waiting') return;
  b.status = 'running';
  const needed = b.cfg.count - b.players.length;
  if (needed > 0) {
    const bots = pickBotNames(needed, botNamesBattles);
    bots.forEach((name) => {
      const team = pickAutoTeam(b);
      b.players.push({ username: name, isBot: true, team, total: 0, lastPull: 0 });
    });
  }
  broadcastBattles();
  runBattle(b);
}

async function runBattle(b) {
  for (let roundIdx = 0; roundIdx < b.caseQueue.length; roundIdx++) {
    const pool = getPool(b.caseQueue[roundIdx]);
    const isFinalRound = roundIdx === b.caseQueue.length - 1;
    const roundPlayers = b.players.map((p) => {
      const pulled = weightedPick(pool);
      p.total = (p.total || 0) + pulled.value;
      if (isFinalRound) p.lastPull = pulled.value; // Terminal only cares about this final-round pull
      return { username: p.username, pulled, total: p.total };
    });
    broadcast({ type: 'casebattle:round', battleId: b.id, roundIdx, players: roundPlayers });
    if (roundIdx < b.caseQueue.length - 1) await new Promise((r) => setTimeout(r, ROUND_PACE_MS));
  }

  const battleTotal = b.players.reduce((s, p) => s + p.total, 0); // winner takes ALL pulled value, not just their own side
  const perPlayerCost = battleCost(b.caseQueue);
  const winMode = WIN_MODES.has(b.winMode) ? b.winMode : 'normal';

  // Group players the same way regardless of mode - teams for Team battles,
  // one group per player for FFA/Group - then each mode below just picks
  // which group wins. This mirrors the client's offline mock exactly, but
  // every number here is computed server-side; the client only animates it.
  let groups;
  if (b.cfg.isTeam) {
    const teamMap = new Map();
    b.players.forEach((p) => {
      if (!teamMap.has(p.team)) {
        teamMap.set(p.team, { key: String(p.team), label: `Team ${String.fromCharCode(65 + Number(p.team))}`, total: 0, lastPull: 0, members: [] });
      }
      const g = teamMap.get(p.team);
      g.total += p.total;
      g.lastPull += (p.lastPull || 0);
      g.members.push(p);
    });
    groups = [...teamMap.values()];
  } else {
    groups = b.players.map((p) => ({ key: p.username, label: p.username, total: p.total, lastPull: p.lastPull || 0, members: [p] }));
  }

  let winningGroups, jackpotInfo = null;
  if (winMode === 'crazy') {
    // Crazy inverts the normal rule: lowest total value wins. A tie for
    // lowest splits the pot across every tied group's members.
    const best = Math.min(...groups.map((g) => g.total));
    winningGroups = groups.filter((g) => g.total === best);
  } else if (winMode === 'terminal') {
    // Terminal ignores the running total entirely - only the single biggest
    // pull from the final case/round decides it. A tie on that final pull
    // splits the pot the same way.
    const best = Math.max(...groups.map((g) => g.lastPull));
    winningGroups = groups.filter((g) => g.lastPull === best);
  } else if (winMode === 'jackpot') {
    // Weighted-random by each group's share of the total pot. The roll and
    // the resulting percentages are both computed here, server-side, so the
    // client's spin animation is just a replay of an already-decided result.
    // A random roll always lands on exactly one group, so there's no tie
    // case to split here even if two groups have identical odds.
    const totalForOdds = groups.reduce((s, g) => s + g.total, 0) || 1;
    let roll = Math.random() * totalForOdds;
    let winningGroup = groups[groups.length - 1];
    let cum = 0;
    for (const g of groups) { cum += g.total; if (roll <= cum) { winningGroup = g; break; } }
    winningGroups = [winningGroup];
    jackpotInfo = groups.map((g) => ({ key: g.key, label: g.label, percent: Math.round((g.total / totalForOdds) * 1000) / 10 }));
  } else {
    // Normal: highest total value wins. A tie for highest splits the pot
    // across every tied group's members.
    const best = Math.max(...groups.map((g) => g.total));
    winningGroups = groups.filter((g) => g.total === best);
  }

  const winner = winningGroups.map((g) => g.label).join(' & '); // e.g. "Team A & Team B" or "alice & bob" on a tie, otherwise just the one label
  const winnerValue = battleTotal; // winning side(s) take the full combined pot, same as before
  const winningMembers = winningGroups.flatMap((g) => g.members);
  const share = Math.floor(battleTotal / Math.max(1, winningMembers.length));

  winningMembers.filter((p) => !p.isBot).forEach((p) => {
    const u = ensureUser(p.username);
    const before = u.coins;
    u.coins += share;
    trackWin(p.username, share);
    persistUser(p.username, { type: 'casebattle_win', amount: share, balanceBefore: before, balanceAfter: u.coins });
    syncAccount(p.username);
  });
  b.players.filter((p) => !winningMembers.includes(p) && !p.isBot).forEach((p) => {
    trackLoss(p.username, perPlayerCost);
    persistUser(p.username, { type: 'casebattle_loss', amount: 0 });
  });

  b.status = 'finished';
  b.winner = winner;
  b.winnerValue = winnerValue;
  broadcastBattles();
  broadcast({
    type: 'casebattle:finished', battleId: b.id, winner, winnerValue, winMode, jackpotInfo,
    // Explicit per-winner personal earnings for the end-of-battle summary
    // screen - `share` here is the exact same value each winning member's
    // account was actually credited with above, not a client-side estimate
    // recomputed from totals. Bots are included (isBot flag) so the client
    // can still show a complete team breakdown for 2v2 without crediting
    // them a real payout.
    winners: winningMembers.map((p) => ({ username: p.username, earnings: share, isBot: !!p.isBot })),
    players: b.players.map((p) => ({ username: p.username, total: p.total, lastPull: p.lastPull || 0 })),
  });
  pushFeedEvent({ game: 'battle', username: winner, amount: winnerValue });

  // Keep the finished result visible for a short window, then drop it from
  // the shared list so the battles view doesn't fill up with stale rows.
  setTimeout(() => {
    const current = battles.get(b.id);
    if (current && current.status === 'finished') {
      battles.delete(b.id);
      broadcastBattles();
    }
  }, CASEBATTLE_FINISHED_DISPLAY_MS);
}

// ---------------------------------------------------------------------------
// Exchange - convert items to coins or coins to items. This was previously
// client-only (never touched the server), which is exactly why a purchase
// looked like it worked locally but the server - which is now the actual
// source of truth for your account - never learned about it.
// ---------------------------------------------------------------------------
const TAX_RATE = 0.05; // must match the client's TAX_RATE

function handleExchangeSell(username, msg) {
  // Sells exactly the requested quantity of each item (how many times its id
  // appears in the array), capped by what's actually owned - not the whole
  // stack regardless of selection, so partial sells work as expected.
  const requested = {};
  for (const id of (msg.items || [])) requested[id] = (requested[id] || 0) + 1;
  const u = ensureUser(username);
  let rawTotal = 0;
  let stockChanged = false;
  const itemsTouched = [];
  for (const [id, reqQty] of Object.entries(requested)) {
    const owned = u.inventory[id] || 0;
    const sellQty = Math.min(reqQty, owned);
    if (sellQty <= 0) continue;
    rawTotal += sellQty * itemValue(id);
    u.inventory[id] = owned - sellQty;
    itemsTouched.push(id);
    // The pet doesn't just vanish - it becomes available for someone
    // else to buy in the Exchange's "coin to item" side.
    shopStock[id] = (shopStock[id] || 0) + sellQty;
    stockChanged = true;
  }
  const before = u.coins;
  const payout = Math.floor(rawTotal * (1 - TAX_RATE));
  u.coins += payout;
  persistUser(username, { type: 'exchange_sell', amount: payout, balanceBefore: before, balanceAfter: u.coins, itemsTouched });
  syncAccount(username);
  if (stockChanged) broadcast({ type: 'exchange:stock', stock: shopStock });
}

function handleExchangeBuy(username, msg) {
  const ids = msg.items || [];
  const requested = {};
  for (const id of ids) requested[id] = (requested[id] || 0) + 1;
  // Every requested pet has to actually be in stock - no more minting pets
  // out of nowhere just because a player has the coins for it.
  for (const [id, reqQty] of Object.entries(requested)) {
    if ((shopStock[id] || 0) < reqQty) {
      return send(usernameToSocket.get(username), { type: 'error', message: `Not enough stock of that item in the Exchange right now.` });
    }
  }
  const cost = ids.reduce((sum, id) => sum + itemValue(id), 0);
  const u = ensureUser(username);
  if (u.coins < cost) return send(usernameToSocket.get(username), { type: 'error', message: `Not enough coins - you need ${cost}.` });
  const before = u.coins;
  u.coins -= cost;
  for (const [id, reqQty] of Object.entries(requested)) shopStock[id] -= reqQty;
  addItems(username, ids);
  persistUser(username, { type: 'exchange_buy', amount: -cost, balanceBefore: before, balanceAfter: u.coins, itemsTouched: [...new Set(ids)] });
  syncAccount(username);
  broadcast({ type: 'exchange:stock', stock: shopStock });
}

// Practice-mode convenience: resets your OWN account back to the starting
// balance. This is intentionally a "give yourself money" cheat - fine for a
// solo hobby server, but if you ever have real friends playing against each
// other here for keeps, you may want to remove this handler so balances
// actually mean something in head-to-head games.
function handleAccountReset(username) {
  if (!ENABLE_DEV_BYPASS) return send(usernameToSocket.get(username), { type: 'error', message: 'That feature is disabled.' });
  const u = ensureUser(username);
  const before = u.coins;
  u.coins = STARTING_BALANCE;
  const itemsTouched = Object.keys(u.inventory);
  u.inventory = {};
  // Zero out every previously-owned item's row too, not just the ones that
  // happened to still be non-zero - a stale row with an old qty would
  // otherwise reappear on the next server restart's DB load.
  persistUser(username, { type: 'account_reset', amount: u.coins - before, balanceBefore: before, balanceAfter: u.coins, itemsTouched, reason: 'Dev bypass: account reset' });
  syncAccount(username);
}

// Admin-only, view-only lookup of another player's current coins/inventory
// - lets the site owner verify a withdrawal claim without being able to
// add, remove, or edit anything in that account. Silently ignored for
// anyone who isn't ADMIN_USERNAME.
// Ranks every account the server has data for by lifetime stats. Bots
// aren't real accounts (never touched via ensureUser), so they naturally
// never appear here - only real players.
const LEADERBOARD_SIZE = 25;
function handleLeaderboardRequest(username) {
  const rows = [...users.entries()]
    // DTN_BGSI (the hand-out/giveaway + trading account) isn't a real
    // player - it exists purely to fund tips/trades, and its stats can run
    // up huge numbers just from moving stock around. It's deliberately
    // excluded from ranking here, same as it's excluded from the account
    // reset script - this only hides it from the leaderboard, its actual
    // stats are untouched.
    .filter(([uname]) => uname.toLowerCase() !== GIVEAWAY_USERNAME.toLowerCase())
    .map(([uname, u]) => ({
      username: uname,
      wagered: (u.stats && u.stats.wagered) || 0,
      won: (u.stats && u.stats.won) || 0,
      lost: (u.stats && u.stats.lost) || 0,
    }));
  const topBy = (key) => rows
    .filter((r) => r[key] > 0)
    .sort((a, b) => b[key] - a[key])
    .slice(0, LEADERBOARD_SIZE)
    .map((r) => ({ username: r.username, value: r[key] }));

  send(usernameToSocket.get(username), {
    type: 'leaderboard:data',
    mostPlayed: topBy('wagered'),
    mostLost: topBy('lost'),
    mostWon: topBy('won'),
  });
}

// Mines, Jackpot, and single Cases still run their actual game logic
// (RNG, tile layout, odds) entirely client-side, same as before - this
// just mirrors the outcome to the server afterward so coins/stats stay
// authoritative and don't get silently overwritten by the next account
// sync. Trust-based (the client reports its own outcome) rather than
// server-verified - reasonable for a small friend-group server, not
// intended to resist a genuinely adversarial client.
//
// `items` is an optional array of catalogIds - Jackpot's pets-staking mode
// stakes items instead of (or alongside) coins, so those need to move in
// and out of inventory here too, not just the coin balance. Without this,
// a client that "removed" staked items locally would just watch them
// reappear on the very next syncAccount, since the server's copy never
// actually changed.
function handleGameWager(username, msg) {
  const amount = Math.max(0, Math.floor(Number(msg.amount) || 0));
  const items = Array.isArray(msg.items) ? msg.items.filter(id => typeof id === 'string') : [];
  if (amount <= 0 && items.length === 0) return;
  if (msg.game === 'mines' && amount > MINES_MAX_BET) {
    return send(usernameToSocket.get(username), { type: 'error', message: `Mines is capped at ${MINES_MAX_BET} coins per round.` });
  }
  const u = ensureUser(username);
  if (amount > u.coins) return; // can't wager more than they actually have
  // Real ownership check before removing anything - without this, staking
  // an item you don't own would silently no-op the removal (clamped at 0)
  // but still count at full catalog value toward the wagered stat, letting
  // anyone inflate their leaderboard standing with items they never
  // actually risked.
  if (items.length && !ownsAll(username, items)) {
    return send(usernameToSocket.get(username), { type: 'error', message: "You don't own those items." });
  }
  const before = u.coins;
  if (amount > 0) u.coins -= amount;
  if (items.length) removeItems(username, items);
  trackWager(username, amount > 0 ? amount : stakeValue(items));
  persistUser(username, { type: `${msg.game || 'game'}_wager`, amount: -amount, balanceBefore: before, balanceAfter: u.coins, itemsTouched: items });
  syncAccount(username);
}

const MINES_MAX_BET = 500000; // must match the client's MINES_MAX_BET
const MINES_VALID_GRID_SIZES = new Set([25, 36, 49, 64]); // 5x5, 6x6, 7x7, 8x8 - must match the client's grid-size buttons

// Mirrors the client's combinations()/minesMultiplier() exactly, so the
// server can independently work out the mathematically maximum legitimate
// payout for a claimed (grid size, mine count, tiles revealed) combination
// and reject anything that claims more than that's actually possible -
// rather than trusting whatever number the client reports outright.
function combinations(n, k) {
  if (k < 0 || k > n) return 0;
  k = Math.min(k, n - k);
  let result = 1;
  for (let i = 0; i < k; i++) result = (result * (n - i)) / (i + 1);
  return result;
}
function minesMultiplier(n, m, picks) {
  if (picks === 0) return 1;
  const HOUSE_EDGE = 0.03;
  const fair = combinations(n, picks) / combinations(n - m, picks);
  return fair * (1 - HOUSE_EDGE);
}

// ---------------------------------------------------------------------------
// Mines - fully server-authoritative. The bomb layout is generated and held
// here only, keyed by username; the client never receives bomb positions
// until the exact moment a tile revealing one is actually clicked (a hit),
// or the round ends and every remaining bomb is revealed for the board
// animation. This replaces the old design where the client generated its
// own bombs and simply self-reported the outcome via a generic
// game:wager/game:resolve pair - that only had a mathematical ceiling on
// the claimed payout, not real verification of what tiles were actually
// safe. game:wager/game:resolve are no longer used by Mines at all now
// (nothing else in the client sends them either), so those two handlers
// above are effectively unused dead code now - left in place rather than
// removed since touching them isn't necessary and isn't worth the risk.
//
// ---------------------------------------------------------------------------
// SINK — a Crash-style rising-multiplier game (there's no pre-existing
// "Crash" implementation in this file to reuse - this is a fresh build,
// following the same server-authoritative model as everything else here:
// the server alone determines the multiplier, the sink point, and every
// payout; the client only ever renders what it's told).
//
// CF coins only - no pets/items accepted as wagers. Capped at
// SINK_MAX_BET per player per round, enforced here server-side regardless
// of what a client sends.
//
// Rounds loop continuously and are shared by everyone (unlike Mines, which
// is one board per player): a 30s joining phase where anyone can place one
// wager, then an active phase of unpredictable length where the multiplier
// climbs from 1.00x until the server's secretly pre-chosen sink point is
// reached, then a short pause showing the result before the next round's
// joining phase begins automatically.
//
// Fairness: the sink point is generated fresh each round the moment the
// active phase begins (generateSinkPoint), using the same "plain
// server-side Math.random(), never revealed until it matters" approach the
// rest of this file already uses for Mines' bomb layout, Dice Duel's
// rolls, etc. - not a cryptographic commit-reveal scheme, consistent with
// how every other game here already works.
//
// The multiplier is never pushed to clients on a timer. Instead, the
// server sends one timestamp (activeStartAt) plus the fixed growth rate
// when the active phase begins, and every client computes and animates
// the climbing number locally from elapsed time - exactly like Jackpot's
// countdown already works. The server independently recomputes the
// multiplier from elapsed time whenever it actually matters (a cashout
// request), so a client can never claim a multiplier it hasn't earned.
// ---------------------------------------------------------------------------
const SINK_MAX_BET = 500000;
const SINK_JOIN_MS = 30000;
const SINK_SUNK_PAUSE_MS = 6000; // how long the result stays up before the next round's joining phase starts
const SINK_GROWTH_K = 0.13; // multiplier(t) = e^(SINK_GROWTH_K * t), t in seconds - reaches ~5x around t=12-13s
const SINK_INSTANT_CHANCE = 0.03; // 3% of rounds sink immediately at 1.00x - this is where the house edge lives

let sinkRound = null; // set by startSinkJoiningPhase() at boot - see server startup below
let sinkTimer = null; // whichever timeout is currently driving the round forward

function sinkMultiplierAt(elapsedSeconds) {
  return Math.exp(SINK_GROWTH_K * elapsedSeconds);
}

// Standard "Crash"-style long-tail distribution: mostly low multipliers,
// occasionally very high ones, with a flat instant-sink chance baked in on
// top for the house edge. 0.99 (rather than 1.00) as the numerator is what
// gives the game its edge on top of the instant-sink chance above.
function generateSinkPoint() {
  if (Math.random() < SINK_INSTANT_CHANCE) return 1.00;
  const r = Math.random(); // (0, 1)
  const raw = 0.99 / (1 - r);
  return Math.max(1.00, Math.floor(raw * 100) / 100);
}

function sinkPublicState(round) {
  const players = [...round.players.entries()].map(([username, p]) => ({
    username, wager: p.wager,
    cashedOutAt: p.cashedOutAt, // multiplier they cashed out at, or null if still in / didn't make it
    payout: p.payout, // null until they cash out
  }));
  const base = { phase: round.phase, players };
  if (round.phase === 'joining') return { ...base, joinEndsAt: round.joinEndsAt };
  if (round.phase === 'active') return { ...base, activeStartAt: round.activeStartAt, growthRate: SINK_GROWTH_K };
  // 'sunk' - safe to reveal the actual sink point now that the round is fully over
  return { ...base, activeStartAt: round.activeStartAt, growthRate: SINK_GROWTH_K, sunkMultiplier: round.sinkPoint };
}

function broadcastSinkState() {
  broadcast({ type: 'sink:state', ...sinkPublicState(sinkRound) });
}

function startSinkJoiningPhase() {
  if (sinkTimer) clearTimeout(sinkTimer);
  sinkRound = {
    phase: 'joining',
    joinEndsAt: Date.now() + SINK_JOIN_MS,
    players: new Map(), // username -> { wager, cashedOutAt, payout }
    activeStartAt: null,
    sinkPoint: null, // chosen (and kept secret) once the active phase starts
  };
  broadcastSinkState();
  sinkTimer = setTimeout(startSinkActivePhase, SINK_JOIN_MS);
}

function startSinkActivePhase() {
  const round = sinkRound;
  if (!round || round.phase !== 'joining') return;
  round.phase = 'active';
  round.activeStartAt = Date.now();
  round.sinkPoint = generateSinkPoint();
  broadcastSinkState();

  const tSinkSeconds = Math.log(round.sinkPoint) / SINK_GROWTH_K;
  sinkTimer = setTimeout(() => resolveSinkRound(round), Math.max(0, tSinkSeconds * 1000));
}

function resolveSinkRound(round) {
  if (!round || round.phase !== 'active' || round !== sinkRound) return;
  round.phase = 'sunk';

  for (const [username, p] of round.players.entries()) {
    if (p.cashedOutAt == null) {
      // Didn't cash out in time - the wager was already deducted at join
      // time, so this is purely recording the loss for stats/feed purposes.
      trackLoss(username, p.wager);
      persistUser(username, { type: 'sink_loss', amount: 0 });
      pushFeedEvent({ game: 'sink', username, amount: p.wager, won: false });
    }
  }

  broadcastSinkState();
  sinkTimer = setTimeout(startSinkJoiningPhase, SINK_SUNK_PAUSE_MS);
}

function handleSinkJoin(username, msg) {
  const errTo = usernameToSocket.get(username);
  if (!sinkRound || sinkRound.phase !== 'joining') {
    return send(errTo, { type: 'error', message: 'SINK is not accepting bets right now - wait for the next round.' });
  }
  if (sinkRound.players.has(username)) {
    return send(errTo, { type: 'error', message: 'You already joined this round.' });
  }

  const amount = Math.floor(Number(msg.amount) || 0);
  if (!amount || amount < 1) return send(errTo, { type: 'error', message: 'Enter a valid amount.' });
  if (amount > SINK_MAX_BET) return send(errTo, { type: 'error', message: `SINK is capped at ${SINK_MAX_BET.toLocaleString()} coins per round.` });

  const u = ensureUser(username);
  if (amount > u.coins) return send(errTo, { type: 'error', message: 'Not enough coins.' });

  const before = u.coins;
  u.coins -= amount;
  sinkRound.players.set(username, { wager: amount, cashedOutAt: null, payout: null });

  trackWager(username, amount);
  persistUser(username, { type: 'sink_wager', amount: -amount, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  broadcastSinkState();
}

function handleSinkCashout(username) {
  const errTo = usernameToSocket.get(username);
  const round = sinkRound;
  if (!round || round.phase !== 'active') {
    return send(errTo, { type: 'error', message: 'There is no active SINK round to cash out of.' });
  }
  const p = round.players.get(username);
  if (!p) return send(errTo, { type: 'error', message: "You didn't join this round." });
  if (p.cashedOutAt != null) return send(errTo, { type: 'error', message: 'You already cashed out this round.' });

  const elapsedSeconds = (Date.now() - round.activeStartAt) / 1000;
  const currentMultiplier = sinkMultiplierAt(elapsedSeconds);
  if (currentMultiplier >= round.sinkPoint) {
    // It sank right as this request arrived - nothing to pay out. The
    // resolve timer handles (or already handled) recording this as a loss.
    return send(errTo, { type: 'error', message: 'Too late - the ship already sank.' });
  }

  const payout = Math.floor(p.wager * currentMultiplier);
  p.cashedOutAt = currentMultiplier;
  p.payout = payout;

  const u = ensureUser(username);
  const before = u.coins;
  u.coins += payout;
  trackWin(username, payout);
  persistUser(username, { type: 'sink_cashout', amount: payout, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  pushFeedEvent({ game: 'sink', username, amount: payout, multiplier: currentMultiplier, won: true });
  broadcastSinkState();
}

// One active round per username at a time (matches how the client only
// ever showed one board anyway). Kept in memory only, same as every other
// live game state in this file - if the process restarts mid-round, that
// round is simply gone, same as it always would have been.
const activeMinesRounds = new Map(); // username -> { n, mCount, gridSize, amount, bombs:Set, revealed:Set, picks, active }

function handleMinesStart(username, msg) {
  const errTo = usernameToSocket.get(username);
  if (activeMinesRounds.has(username)) {
    return send(errTo, { type: 'error', message: 'You already have an active Mines round.' });
  }

  const amount = Math.max(0, Math.floor(Number(msg.amount) || 0));
  const mCount = Math.floor(Number(msg.mineCount));
  const gridSize = Math.floor(Number(msg.gridSize));
  const n = gridSize * gridSize;

  if (!amount || amount < 1) return send(errTo, { type: 'error', message: 'Enter a valid amount.' });
  if (amount > MINES_MAX_BET) return send(errTo, { type: 'error', message: `Mines is capped at ${MINES_MAX_BET} coins per round.` });
  if (!MINES_VALID_GRID_SIZES.has(n)) return send(errTo, { type: 'error', message: 'Invalid grid size.' });
  if (!mCount || mCount < 1 || mCount >= n) return send(errTo, { type: 'error', message: 'Invalid mine count.' });

  const u = ensureUser(username);
  if (amount > u.coins) return send(errTo, { type: 'error', message: 'Not enough coins.' });

  const before = u.coins;
  u.coins -= amount;

  // Fisher-Yates partial shuffle to pick mCount unique bomb tiles out of n -
  // simple, correct, and the result is never sent to the client up front.
  const positions = Array.from({ length: n }, (_, i) => i);
  for (let i = positions.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [positions[i], positions[j]] = [positions[j], positions[i]];
  }
  const bombs = new Set(positions.slice(0, mCount));

  activeMinesRounds.set(username, { n, mCount, gridSize, amount, bombs, revealed: new Set(), picks: 0, active: true });

  trackWager(username, amount);
  persistUser(username, { type: 'mines_wager', amount: -amount, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  send(errTo, { type: 'mines:started', n, mCount, gridSize, amount });
}

function handleMinesReveal(username, msg) {
  const errTo = usernameToSocket.get(username);
  const round = activeMinesRounds.get(username);
  if (!round || !round.active) return send(errTo, { type: 'error', message: 'No active Mines round.' });

  const tileIndex = Math.floor(Number(msg.tileIndex));
  if (!Number.isInteger(tileIndex) || tileIndex < 0 || tileIndex >= round.n) {
    return send(errTo, { type: 'error', message: 'Invalid tile.' });
  }
  if (round.revealed.has(tileIndex)) {
    return send(errTo, { type: 'error', message: 'That tile is already revealed.' });
  }
  round.revealed.add(tileIndex);

  if (round.bombs.has(tileIndex)) {
    round.active = false;
    activeMinesRounds.delete(username);
    trackLoss(username, round.amount);
    persistUser(username, { type: 'mines_loss', amount: 0 });
    // The round is over - safe to reveal every bomb now for the board
    // animation, since none of these positions were ever sent before this.
    send(errTo, { type: 'mines:hit', tileIndex, bombs: [...round.bombs] });
    pushFeedEvent({ game: 'mines', username, amount: round.amount, won: false });
    return;
  }

  round.picks++;
  const multiplier = minesMultiplier(round.n, round.mCount, round.picks);
  const currentPayout = Math.floor(round.amount * multiplier);
  const safeTilesTotal = round.n - round.mCount;

  if (round.picks === safeTilesTotal) {
    // Every safe tile revealed - auto cash out, matching existing behavior.
    const u = ensureUser(username);
    const before = u.coins;
    u.coins += currentPayout;
    trackWin(username, currentPayout);
    round.active = false;
    activeMinesRounds.delete(username);
    persistUser(username, { type: 'mines_resolve', amount: currentPayout, balanceBefore: before, balanceAfter: u.coins });
    syncAccount(username);
    send(errTo, { type: 'mines:revealed', tileIndex, multiplier, payout: currentPayout, picks: round.picks, fullClear: true });
    pushFeedEvent({ game: 'mines', username, amount: currentPayout, multiplier, won: true });
    return;
  }

  send(errTo, { type: 'mines:revealed', tileIndex, multiplier, payout: currentPayout, picks: round.picks, fullClear: false });
}

function handleMinesCashout(username) {
  const errTo = usernameToSocket.get(username);
  const round = activeMinesRounds.get(username);
  if (!round || !round.active) return send(errTo, { type: 'error', message: 'No active Mines round.' });
  if (round.picks === 0) return send(errTo, { type: 'error', message: 'Reveal at least one tile before cashing out.' });

  const multiplier = minesMultiplier(round.n, round.mCount, round.picks);
  const payout = Math.floor(round.amount * multiplier);

  round.active = false;
  activeMinesRounds.delete(username);

  const u = ensureUser(username);
  const before = u.coins;
  u.coins += payout;
  trackWin(username, payout);
  persistUser(username, { type: 'mines_resolve', amount: payout, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  send(errTo, { type: 'mines:cashedOut', payout, multiplier });
  pushFeedEvent({ game: 'mines', username, amount: payout, multiplier, won: true });
}

function handleGameResolve(username, msg) {
  const payout = Math.max(0, Math.floor(Number(msg.payout) || 0));
  const wager = Math.max(0, Math.floor(Number(msg.wager) || 0));

  // WHITELIST, not blacklist: game:resolve only ever pays out for games
  // explicitly listed here. Cases used to be accepted here too and paid out
  // whatever the client claimed it won - now cases go through the fully
  // server-authoritative case:open handler instead, and this endpoint
  // rejects anything that isn't on the list below, no matter what game
  // string is sent. If you're adding a new game here, it needs the same
  // server-side outcome verification mines has (the wager cap below) or
  // its own dedicated authoritative handler like case:open - never blindly
  // trust a client-reported payout.
  const ALLOWED_RESOLVE_GAMES = new Set(['mines']);
  if (!ALLOWED_RESOLVE_GAMES.has(msg.game)) return;

  // Belt-and-suspenders: the client already stops you from starting a Mines
  // round above this, but don't trust that alone - reject anything that
  // claims a bigger wager was involved.
  if (msg.game === 'mines' && wager > MINES_MAX_BET) {
    return send(usernameToSocket.get(username), { type: 'error', message: `Mines is capped at ${MINES_MAX_BET} coins per round.` });
  }
  // The actual reveal-by-reveal Mines round still plays out client-side
  // (no per-tile round trip to the server), so this can't verify the exact
  // tiles that were revealed - but it CAN verify the claim is mathematically
  // possible at all. A claimed win reports the grid size, mine count, and
  // how many safe tiles were revealed; the server recomputes the real
  // maximum multiplier for that exact shape using the same formula the
  // client uses, and rejects anything claiming more than that - so instead
  // of "type any number you want," the ceiling is now "the best possible
  // truthful outcome for whatever round shape you claim happened."
  if (msg.game === 'mines' && payout > 0) {
    const n = Math.floor(Number(msg.n));
    const mCount = Math.floor(Number(msg.mCount));
    const picks = Math.floor(Number(msg.picks));
    const validShape = MINES_VALID_GRID_SIZES.has(n) && mCount >= 1 && mCount <= n - 1 && picks >= 1 && picks <= n - mCount;
    if (!validShape) {
      return send(usernameToSocket.get(username), { type: 'error', message: 'Invalid Mines round - payout rejected.' });
    }
    const maxMultiplier = minesMultiplier(n, mCount, picks);
    const maxPayout = wager * maxMultiplier;
    if (payout > maxPayout * 1.0001) { // tiny tolerance for floating-point rounding, not a real gap
      return send(usernameToSocket.get(username), { type: 'error', message: 'That payout is higher than mathematically possible for this round - rejected.' });
    }
  }
  const u = ensureUser(username);
  const before = u.coins;
  if (payout > 0) {
    u.coins += payout;
    trackWin(username, payout);
  } else if (wager > 0) {
    trackLoss(username, wager);
  }
  // Mines (the only game left on this endpoint) never legitimately awards
  // items, only coins - so items from the client are never trusted or
  // credited here at all, closing off what would otherwise be another
  // "just add whatever catalog ids you want" gap even after the payout
  // itself got locked down above.
  persistUser(username, { type: `${msg.game || 'game'}_resolve`, amount: payout, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);

  // Feed it to the site-wide live feed too (Coinflip/Battles/Jackpot log
  // their own feed entries directly at the point they resolve).
  if (payout > 0) {
    const multiplier = Number(msg.multiplier) || (wager > 0 ? payout / wager : 0);
    pushFeedEvent({ game: 'mines', username, amount: payout, multiplier, won: true });
  } else if (wager > 0) {
    pushFeedEvent({ game: 'mines', username, amount: wager, won: false });
  }
}

// Server-authoritative single case opening. This exists specifically to
// close a real exploit: the previous flow let the client run its own
// weightedPick() locally and simply report the "result" via game:resolve,
// which the server credited unconditionally - anyone could fabricate a
// win of the rarest item in the catalog via devtools with no actual roll.
// Here the price, the roll, and the resulting payout are all decided
// server-side against the real catalog pool (casePools) - the client only
// gets told what it won after the fact, purely for the reel animation.
// Matches the existing game design: pulls convert straight to coins, no
// inventory item is ever actually added.
function handleCaseOpen(username, msg) {
  const errTo = usernameToSocket.get(username);
  const caseIndex = Math.floor(Number(msg.caseIndex));
  const c = caseData[caseIndex];
  if (!c) return send(errTo, { type: 'error', message: 'That case does not exist.' });
  const pool = casePools['b' + caseIndex];
  if (!pool || !pool.length) return send(errTo, { type: 'error', message: 'That case has no items configured yet.' });

  const u = ensureUser(username);
  if (u.coins < c.price) return send(errTo, { type: 'error', message: "You don't have enough coins for this case." });

  const before = u.coins;
  u.coins -= c.price;

  const total = pool.reduce((s, e) => s + e.chance, 0);
  let roll = Math.random() * total;
  let wonEntry = pool[pool.length - 1];
  for (const entry of pool) {
    roll -= entry.chance;
    if (roll <= 0) { wonEntry = entry; break; }
  }
  const wonId = wonEntry.id;
  const wonPet = petCatalog[wonId];
  if (!wonPet) {
    // Data integrity problem (a pool entry pointing at a catalog id that
    // doesn't exist) - refund rather than silently eat their coins.
    u.coins = before;
    return send(errTo, { type: 'error', message: 'Something went wrong opening that case - try again.' });
  }

  // A pool entry can carry its own "value" that overrides the pet's real
  // catalog value - lets a case reuse existing pet art/names at a payout
  // specific to that case (same design as Case Battles' caseItems), without
  // touching the pet's value everywhere else it appears.
  const payout = (typeof wonEntry.value === 'number') ? wonEntry.value : wonPet.value;

  u.coins += payout; // pulls convert straight to coins, matching the existing "no inventory needed" case design
  trackWager(username, c.price);
  persistUser(username, { type: 'case_open', amount: payout - c.price, balanceBefore: before, balanceAfter: u.coins });
  syncAccount(username);
  send(errTo, {
    type: 'case:opened',
    caseIndex,
    wonId,
    name: wonPet.name,
    value: payout,
    rarity: wonPet.rarity,
    pool: pool.map((e) => ({ id: e.id, chance: e.chance, value: e.value })),
  });
  pushFeedEvent({ game: 'cases', username, amount: payout, itemName: wonPet.name });
}

async function handleAdminLookup(username, msg) {
  if (username !== ADMIN_USERNAME) return;
  const rawTarget = String(msg.username || '');
  const resolved = resolveExistingUsername(rawTarget);
  // ensureUser() (not a plain users.get()) so an existing account's
  // self-healing runs before we display it - otherwise a real account
  // that just hasn't been touched since a new pet was added to the
  // catalog would show as "missing" items that have actually already
  // been backfilled for everyone else who's logged in since.
  const u = resolved ? ensureUser(resolved) : null;
  const target = resolved || rawTarget;
  let transactions = [];
  if (u) {
    try {
      transactions = await db.loadRecentTransactionsForUser(target, 15);
    } catch (err) {
      console.error(`[db] Failed to load transaction history for ${target}:`, err.message);
    }
  }
  send(usernameToSocket.get(username), {
    type: 'admin:lookupResult',
    username: target,
    found: !!u,
    coins: u ? u.coins : null,
    inventory: u ? u.inventory : null,
    stats: u ? u.stats : null,
    transactions,
  });
}

// Admin-only balance adjustment - covers both "add coins" and "remove
// coins" (removeCoins is just addCoins with a negated, clamped amount).
// Every call writes a real transaction row via the same persistUser() path
// every other coin-mutating action already uses, so this shows up in the
// user's transaction history exactly like a game payout or a tip would,
// just tagged as an admin action with who did it and why.
async function handleAdminAdjustCoins(username, msg, direction) {
  if (username !== ADMIN_USERNAME) return;
  const errTo = usernameToSocket.get(username);
  const rawTarget = String(msg.username || '');
  const amount = Math.floor(Number(msg.amount) || 0);
  const reason = String(msg.reason || '').slice(0, 200) || (direction > 0 ? 'Admin coin grant' : 'Admin coin removal');
  if (!rawTarget || amount <= 0) {
    return send(errTo, { type: 'error', message: 'Enter a username and a positive amount.' });
  }
  const resolved = resolveExistingUsername(rawTarget);
  if (!resolved && direction < 0) {
    return send(errTo, { type: 'error', message: `No account found for "${rawTarget}".` });
  }
  // Adding coins is allowed to create the account fresh if it doesn't exist
  // yet (e.g. funding BloxyVault_Stock or DTN_BGSI before they've ever
  // logged in) - same idea as tipping someone who hasn't logged in yet.
  // Removing from nothing doesn't make sense, so that still requires a
  // real existing account (checked above).
  const target = resolved || rawTarget;
  const u = ensureUser(target);
  const before = u.coins;
  const delta = direction > 0 ? amount : -Math.min(amount, u.coins); // never push a balance negative
  u.coins += delta;
  persistUser(target, {
    type: 'admin_adjust',
    amount: delta,
    balanceBefore: before,
    balanceAfter: u.coins,
    reason,
    adminUsername: username,
  });
  syncAccount(target);
  send(errTo, { type: 'admin:adjustResult', username: target, ok: true, coins: u.coins, delta });
}
// pets out for the real Roblox items", the admin sees the request (plus can
// double-check their actual inventory via admin:lookup above to make sure
// they're not lying about what they have), does the real-world trade
// themselves outside this app, then marks it fulfilled here - which is what
// actually removes the items, so there's a clear log of who asked for what
// and when, rather than silent inventory edits with no trail.
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Withdrawal requests - a real player says "I want to cash these specific
// pets out for the real Roblox items", the admin sees the request (plus can
// double-check their actual inventory via admin:lookup above to make sure
// they're not lying about what they have), does the real-world trade
// themselves outside this app, then marks it fulfilled here - which is what
// actually removes the items, so there's a clear log of who asked for what
// and when, rather than silent inventory edits with no trail.
// ---------------------------------------------------------------------------
let withdrawRequests = []; // { id, username, items, requestedAt, status, actuallyRemoved? }
const MAX_WITHDRAW_ITEMS = 8;

async function handleWithdrawRequest(username, msg) {
  const items = msg.items || [];
  const errTo = usernameToSocket.get(username);
  if (!items.length) return send(errTo, { type: 'error', message: 'Select at least one item to withdraw.' });
  if (items.length > MAX_WITHDRAW_ITEMS) return send(errTo, { type: 'error', message: `You can withdraw at most ${MAX_WITHDRAW_ITEMS} pets at a time.` });
  if (!ownsAll(username, items)) return send(errTo, { type: 'error', message: "You don't own all of those items." });

  const req = { id: 'wd_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8), username, items, requestedAt: Date.now(), status: 'pending' };
  try {
    await db.insertWithdrawRequest(req);
  } catch (err) {
    console.error(`[db] Failed to persist withdraw request for ${username}:`, err.message);
    return send(errTo, { type: 'error', message: 'Something went wrong submitting that - try again in a moment.' });
  }
  withdrawRequests.push(req);
  send(errTo, { type: 'withdraw:requested', id: req.id });
  // Immediately pushes the now-locked items out of their available
  // inventory client-side (My Items, Coinflip/Jackpot/Dice Duel/Exchange
  // pickers, etc.) so they physically can't select and gamble away pets
  // that are sitting in a pending withdrawal request.
  syncAccount(username);
  broadcastPendingWithdrawalsToAdmin();
}

function broadcastPendingWithdrawalsToAdmin(){
  const adminWs = usernameToSocket.get(ADMIN_USERNAME);
  if (!adminWs) return;
  send(adminWs, { type: 'admin:withdrawList', requests: withdrawRequests.filter(r => r.status === 'pending') });
}

function handleAdminWithdrawList(username) {
  if (username !== ADMIN_USERNAME) return;
  broadcastPendingWithdrawalsToAdmin();
}

async function handleAdminWithdrawFulfill(username, msg) {
  if (username !== ADMIN_USERNAME) return;
  const req = withdrawRequests.find(r => r.id === msg.requestId && r.status === 'pending');
  if (!req) return;

  // Remove exactly what's requested, capped by whatever they still actually
  // own right now (they may have sold/lost/traded something since asking) -
  // and report back precisely what was removed, so any mismatch is visible
  // rather than silently over- or under-removing.
  const target = ensureUser(req.username);
  const requested = {};
  for (const id of req.items) requested[id] = (requested[id] || 0) + 1;
  const actuallyRemoved = {};
  for (const [id, reqQty] of Object.entries(requested)) {
    const owned = target.inventory[id] || 0;
    const removeQty = Math.min(reqQty, owned);
    if (removeQty > 0) { target.inventory[id] = owned - removeQty; actuallyRemoved[id] = removeQty; }
  }

  // The DB row is the actual source of truth for "has this already been
  // actioned" - this only succeeds if it's still 'pending' there right now,
  // so two admin clicks (or a retry) can never both go through and remove
  // items twice, even if the in-memory array briefly disagreed.
  let ok;
  try {
    ok = await db.resolveWithdrawRequest(req.id, 'pending', 'fulfilled', actuallyRemoved);
  } catch (err) {
    console.error(`[db] Failed to resolve withdraw request ${req.id}:`, err.message);
    return;
  }
  if (!ok) return; // someone/something else already resolved this request

  req.status = 'fulfilled';
  req.actuallyRemoved = actuallyRemoved;
  persistUser(req.username, { type: 'withdraw_fulfilled', amount: 0, itemsTouched: Object.keys(actuallyRemoved), reason: `Fulfilled by ${ADMIN_USERNAME}`, adminUsername: ADMIN_USERNAME });
  syncAccount(req.username);
  send(usernameToSocket.get(req.username), { type: 'chat:message', username: 'System', text: `Your withdrawal request was fulfilled by ${ADMIN_USERNAME}.`, timestamp: Date.now(), system: true });
  broadcastPendingWithdrawalsToAdmin();
}

async function handleAdminWithdrawReject(username, msg) {
  if (username !== ADMIN_USERNAME) return;
  const req = withdrawRequests.find(r => r.id === msg.requestId && r.status === 'pending');
  if (!req) return;
  let ok;
  try {
    ok = await db.resolveWithdrawRequest(req.id, 'pending', 'rejected', null);
  } catch (err) {
    console.error(`[db] Failed to resolve withdraw request ${req.id}:`, err.message);
    return;
  }
  if (!ok) return; // already resolved
  req.status = 'rejected';
  persistUser(req.username, { type: 'withdraw_rejected', amount: 0, reason: `Rejected by ${ADMIN_USERNAME}`, adminUsername: ADMIN_USERNAME });
  syncAccount(req.username); // unlocks the items back into their available inventory
  send(usernameToSocket.get(req.username), { type: 'error', message: 'Your withdrawal request was declined.' });
  broadcastPendingWithdrawalsToAdmin();
}

async function handleWithdrawCancel(username, msg) {
  // Cancelling has been disabled - once submitted, a withdrawal request is
  // locked in for admin review one way or the other (fulfilled/rejected),
  // rather than something a player can pull back at will. The client no
  // longer offers a Cancel button, but this stays as a hard no-op (instead
  // of just removing the case entirely) so a direct/tampered
  // withdraw:cancel message can't do it either.
  const errTo = usernameToSocket.get(username);
  if (errTo) send(errTo, { type: 'error', message: "Withdrawal requests can't be cancelled once submitted." });
}


// ---------------------------------------------------------------------------
// Chat - real, shared, no bots. Very light rate limiting (one message per
// 500ms per connection) just to stop an accidental flood from one client.
// ---------------------------------------------------------------------------
const lastChatAt = new Map(); // ws -> timestamp

// Moderators get ONLY this one permission (mute/unmute) - deliberately kept
// completely separate from ADMIN_USERNAME checks everywhere else in the
// file (coin adjustments, withdrawals, role granting, etc. all still check
// ADMIN_USERNAME alone, untouched by this). This is the sole place a
// moderator's specialRole grants any actual capability.
function isModOrAdmin(username) {
  if (username === ADMIN_USERNAME) return true;
  const u = users.get(username);
  return !!u && u.specialRole === 'moderator';
}

const MAX_MUTE_MS = 24 * 60 * 60 * 1000; // hard cap - no accidental/malicious "forever" mutes
// Parses "30m", "1h", "1h30m", "2h" etc. Returns milliseconds, or null if it
// doesn't look like a valid duration at all.
function parseMuteDuration(str) {
  const s = String(str || '').trim().toLowerCase();
  const m = s.match(/^(?:(\d+)h)?(?:(\d+)m)?$/);
  if (!m || (!m[1] && !m[2])) return null;
  const hours = parseInt(m[1] || '0', 10);
  const mins = parseInt(m[2] || '0', 10);
  const totalMs = (hours * 60 + mins) * 60 * 1000;
  if (totalMs <= 0) return null;
  return Math.min(totalMs, MAX_MUTE_MS);
}
function formatMuteDuration(ms) {
  const totalMin = Math.round(ms / 60000);
  const h = Math.floor(totalMin / 60), m = totalMin % 60;
  if (h > 0 && m > 0) return `${h}h${m}m`;
  if (h > 0) return `${h}h`;
  return `${m}m`;
}

// ---------------------------------------------------------------------------
// EMERGENCY LOCKDOWN — an instant, admin-toggleable kill switch (see the
// /lockdown chat command in handleChatSend) for "something's badly wrong,
// freeze everything right now" situations, without needing to redeploy or
// even restart the server. While active:
//   - Non-admin logins are rejected outright (see the login handler above).
//   - Every message type in LOCKDOWN_BLOCKED_TYPES is rejected for anyone
//     already connected (defense in depth, in case someone was mid-session
//     when lockdown was triggered).
// Purely in-memory - resets to off on restart, same as everything else
// here. Chat, the leaderboard, and viewing a profile still work during
// lockdown so people aren't left completely in the dark about what's
// happening; every action that actually touches coins/items/escrow does not.
let siteLockdown = false;
const LOCKDOWN_BLOCKED_TYPES = new Set([
  'rain:deposit', 'rain:claim',
  'coinflip:create', 'coinflip:join', 'coinflip:cancel',
  'diceduel:create', 'diceduel:join', 'diceduel:cancel',
  'jackpot:enter',
  'casebattle:create', 'casebattle:join', 'casebattle:start', 'casebattle:callBot', 'casebattle:cancel',
  'exchange:sell', 'exchange:buy',
  'account:reset',
  'game:wager', 'game:resolve',
  'case:open',
  'mines:start', 'mines:reveal', 'mines:cashout',
  'withdraw:request', 'withdraw:cancel',
  'tip:send',
  'sink:join', 'sink:cashout',
]);

function handleChatSend(username, msg, ws) {
  const now = Date.now();
  if (now - (lastChatAt.get(ws) || 0) < 500) return;
  lastChatAt.set(ws, now);
  const text = String(msg.text || '').slice(0, 70).trim();
  if (!text) return;

  // /mute, /unmute, and /lockdown are commands, not real chat messages -
  // they never get broadcast as text even if a non-mod/non-admin types
  // them (the permission check below just quietly rejects it with a
  // private error, same as if they'd tried any other admin action they
  // don't have).
  const muteMatch = text.match(/^\/mute\s+(\S+)\s+(\S+)/i);
  const unmuteMatch = !muteMatch && text.match(/^\/unmute\s+(\S+)/i);
  const lockdownMatch = !muteMatch && !unmuteMatch && text.match(/^\/lockdown\s+(on|off)/i);
  if (lockdownMatch) {
    // Deliberately stricter than /mute's isModOrAdmin - this freezes every
    // player's ability to touch coins/items/escrow site-wide, so it's
    // restricted to the actual site owner only, not moderators.
    if (username !== ADMIN_USERNAME) {
      return send(usernameToSocket.get(username), { type: 'error', message: "You don't have permission to do that." });
    }
    const turningOn = lockdownMatch[1].toLowerCase() === 'on';
    if (turningOn === siteLockdown) {
      return send(usernameToSocket.get(username), { type: 'toast', message: `Lockdown is already ${turningOn ? 'ON' : 'OFF'}.` });
    }
    siteLockdown = turningOn;
    send(usernameToSocket.get(username), { type: 'toast', message: `Site lockdown is now ${turningOn ? 'ON' : 'OFF'}.` });
    pushChatMessage({
      username: 'System',
      text: turningOn
        ? '🔒 The site has been locked down by an admin. All gameplay is paused until further notice.'
        : '🔓 The lockdown has been lifted. Gameplay is back to normal.',
      timestamp: now, wagered: 0, system: true,
    });
    return;
  }
  if (muteMatch || unmuteMatch) {
    if (!isModOrAdmin(username)) {
      return send(usernameToSocket.get(username), { type: 'error', message: "You don't have permission to do that." });
    }
    if (muteMatch) {
      const targetName = muteMatch[1];
      const durationMs = parseMuteDuration(muteMatch[2]);
      if (!durationMs) {
        return send(usernameToSocket.get(username), { type: 'error', message: 'Usage: /mute username 30m (or 1h, 1h30m, etc. - max 24h).' });
      }
      const targetUser = ensureUser(targetName);
      if (targetName === ADMIN_USERNAME) {
        return send(usernameToSocket.get(username), { type: 'error', message: "Can't mute the admin account." });
      }
      targetUser.mutedUntil = now + durationMs;
      const label = formatMuteDuration(durationMs);
      send(usernameToSocket.get(username), { type: 'toast', message: `Muted ${targetName} for ${label}.` });
      const targetWs = usernameToSocket.get(targetName);
      if (targetWs) send(targetWs, { type: 'toast', message: `You've been muted for ${label} by a moderator.`, isError: true });
      pushChatMessage({ username: 'System', text: `${targetName} was muted for ${label}.`, timestamp: now, wagered: 0, system: true });
    } else {
      const targetName = unmuteMatch[1];
      const targetUser = ensureUser(targetName);
      targetUser.mutedUntil = 0;
      send(usernameToSocket.get(username), { type: 'toast', message: `Unmuted ${targetName}.` });
      const targetWs = usernameToSocket.get(targetName);
      if (targetWs) send(targetWs, { type: 'toast', message: `You've been unmuted.` });
      pushChatMessage({ username: 'System', text: `${targetName} was unmuted.`, timestamp: now, wagered: 0, system: true });
    }
    return;
  }

  const u = ensureUser(username);
  if (u.mutedUntil && u.mutedUntil > now) {
    const remainingLabel = formatMuteDuration(u.mutedUntil - now);
    return send(usernameToSocket.get(username), { type: 'error', message: `You're muted for another ${remainingLabel}.` });
  }

  const wagered = u.stats.wagered || 0;
  pushChatMessage({ username, text, timestamp: now, wagered, specialRole: u.specialRole || null });
}

// ---------------------------------------------------------------------------
// Public profile lookup - clicking any avatar site-wide requests this for
// the clicked user. Only ever returns PUBLIC game stats (wagered/won/lost)
// and whether they're the admin account - never balance, inventory, or
// anything else private. Looks the user up (creating their record if this
// is literally the first time anyone's referenced them) rather than trusting
// anything the client already thinks it knows about that user.
// ---------------------------------------------------------------------------
function handleProfileRequest(username, msg) {
  const targetName = String(msg.username || '').trim();
  if (!targetName) return;
  const u = ensureUser(targetName);
  send(usernameToSocket.get(username), {
    type: 'profile:data',
    username: targetName,
    stats: { wagered: u.stats.wagered || 0, won: u.stats.won || 0, lost: u.stats.lost || 0 },
    isAdmin: targetName === ADMIN_USERNAME,
    specialRole: u.specialRole || null,
  });
}

const GRANTABLE_ROLES = new Set(['vip', 'moderator']);
// Manually-assigned roles (VIP / Moderator) - separate from the automatic
// wagered-based milestone roles, which are never stored anywhere since
// they're always derived live from stats.wagered (so they can never be
// stale, faked, or handed out early). These two ARE stored, since they're
// not tied to any measurable progress - only the real admin account can
// grant or remove one, checked here server-side regardless of what the
// client claims; the target user's own connection (if online) also gets a
// fresh sync so it takes effect immediately for them too, not just for
// whoever's viewing their profile.
function handleAdminSetRole(username, msg) {
  if (username !== ADMIN_USERNAME) return; // never trust a client claiming to be the admin
  const targetName = String(msg.targetUsername || '').trim();
  if (!targetName) return;
  const role = msg.role === null ? null : String(msg.role || '');
  if (role !== null && !GRANTABLE_ROLES.has(role)) return;
  const u = ensureUser(targetName);
  const before = u.specialRole || null;
  u.specialRole = role;
  persistUser(targetName, { type: 'admin_set_role', amount: 0, reason: `${before || 'none'} -> ${role || 'none'} (by ${username})` });
  syncAccount(targetName); // updates their own client immediately if they're online
  send(usernameToSocket.get(username), { type: 'profile:data', username: targetName, stats: { wagered: u.stats.wagered || 0, won: u.stats.won || 0, lost: u.stats.lost || 0 }, isAdmin: targetName === ADMIN_USERNAME, specialRole: u.specialRole || null });
}

// ---------------------------------------------------------------------------
// Tipping - coins and/or items, direct account-to-account transfer.
// ---------------------------------------------------------------------------
function handleTipSend(username, msg) {
  const rawTo = String(msg.toUsername || '').trim();
  const coins = Math.max(0, Math.floor(Number(msg.coins) || 0));
  const items = Array.isArray(msg.items) ? msg.items : [];
  const errTo = usernameToSocket.get(username);

  if (!rawTo) return send(errTo, { type: 'error', message: 'Pick someone else to tip.' });
  // Route to a real, already-known account if one matches case-insensitively
  // (e.g. typing "alice" when the real account is "Alice") - otherwise this
  // silently creates a brand-new phantom account under whatever casing was
  // typed, the coins/items land there instead of the real person, and it
  // looks to the sender like the tip "went through" while the intended
  // recipient's balance never actually changes. Only fall back to creating
  // a fresh account if genuinely nobody matches - that's the intentional
  // "tip a friend before they've ever logged in" case.
  const toUsername = resolveExistingUsername(rawTo) || rawTo;
  if (toUsername.toLowerCase() === username.toLowerCase()) return send(errTo, { type: 'error', message: 'Pick someone else to tip.' });
  if (coins <= 0 && !items.length) return send(errTo, { type: 'error', message: 'Add some coins or items to tip.' });

  const u = ensureUser(username);
  const target = ensureUser(toUsername); // creates their account if they haven't logged in yet this session - the tip just waits for them
  if (coins > 0 && u.coins < coins) return send(errTo, { type: 'error', message: "You don't have that many coins." });
  if (items.length && !ownsAll(username, items)) return send(errTo, { type: 'error', message: "You don't own all of those items." });

  const senderBefore = u.coins;
  const targetBefore = target.coins;
  if (coins > 0) { u.coins -= coins; target.coins += coins; }
  let senderItemsTouched = [];
  if (items.length) {
    // The giveaway account's stock never runs out - only credit the
    // recipient, don't deduct from the sender, so it stays at 99x forever.
    if (username.toLowerCase() !== GIVEAWAY_USERNAME.toLowerCase()) { removeItems(username, items); senderItemsTouched = [...new Set(items)]; }
    addItems(toUsername, items);
  }

  persistUser(username, { type: 'tip_send', amount: -coins, balanceBefore: senderBefore, balanceAfter: u.coins, itemsTouched: senderItemsTouched, reason: `To ${toUsername}` });
  persistUser(toUsername, { type: 'tip_receive', amount: coins, balanceBefore: targetBefore, balanceAfter: target.coins, itemsTouched: [...new Set(items)], reason: `From ${username}` });
  syncAccount(username);
  syncAccount(toUsername);

  const parts = [];
  if (coins > 0) parts.push(`${coins.toLocaleString()} coins`);
  if (items.length) parts.push(`${items.length} item${items.length > 1 ? 's' : ''}`);
  pushChatMessage({ username: 'System', text: `${username} tipped ${toUsername} ${parts.join(' + ')}`, timestamp: Date.now(), system: true });
}

// ---------------------------------------------------------------------------
// Connection lifecycle
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Roblox lookups - resolves username/avatar/bio-verification server-side.
// This exists because browsers can't call Roblox's API directly (no CORS
// headers on Roblox's end), and public CORS-relay services turned out to be
// unreliable in practice (ad blockers and privacy tools commonly block
// exactly this kind of proxy domain). A server has no CORS restrictions at
// all, so this is both simpler and far more reliable than relay-hopping.
// ---------------------------------------------------------------------------
// Small retry wrapper for outbound Roblox API calls. Unlike the browser,
// the server has no CORS restriction talking to Roblox directly - so a
// failed call here is a genuine transient network blip, not a
// browser-security limitation, and the right fix is just to retry a couple
// of times before giving up, not to hand verification off to the client.
async function fetchWithRetry(url, attempts = 3) {
  let lastErr;
  for (let i = 0; i < attempts; i++) {
    // Without a hard timeout here, a slow/unresponsive Roblox API can hang
    // this call indefinitely - and with no response ever written, Railway's
    // own edge eventually gives up waiting and substitutes its own generic
    // error page (an empty 404 with no trace of anything this file ever
    // wrote), which looks nothing like the actual 502 this function's own
    // caller would otherwise send. Bounding each attempt means we always
    // get the chance to respond with a real, informative error ourselves.
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 8000);
    try {
      const r = await fetch(url, { signal: controller.signal });
      if (!r.ok) throw new Error(`HTTP ${r.status}`);
      return r;
    } catch (err) {
      lastErr = err;
      if (i < attempts - 1) await new Promise((resolve) => setTimeout(resolve, 500 * (i + 1)));
    } finally {
      clearTimeout(timeoutId);
    }
  }
  throw lastErr;
}

async function robloxResolveUsername(username){
  const r = await fetchWithRetry(`https://users.roblox.com/v1/users/search?keyword=${encodeURIComponent(username)}&limit=10`);
  const data = await r.json();
  return (data.data || []).find((u) => (u.name || '').toLowerCase() === username.toLowerCase()) || null;
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${req.headers.host}`);

  // These are read-only public Roblox lookups triggered by the client's own
  // pages (GitHub Pages, wherever it's hosted) - nothing sensitive, so allow
  // any origin to call them.
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
  if(req.method === 'OPTIONS'){ res.writeHead(204); res.end(); return; }

  if(url.pathname === '/roblox/resolve'){
    const username = url.searchParams.get('username') || '';
    try{
      const match = await robloxResolveUsername(username);
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ found: !!match, userId: match ? match.id : null }));
    } catch(e){
      res.writeHead(502, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ found: false, userId: null, error: 'roblox_unreachable' }));
    }
    return;
  }

  if(url.pathname === '/roblox/avatar'){
    const username = url.searchParams.get('username') || '';
    try{
      const match = await robloxResolveUsername(username);
      if(!match){ res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ imageUrl: null })); return; }
      const thumbR = await fetchWithRetry(`https://thumbnails.roblox.com/v1/users/avatar-headshot?userIds=${match.id}&size=150x150&format=Png&isCircular=false`);
      const thumbData = await thumbR.json();
      const entry = (thumbData.data || [])[0];
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ imageUrl: entry && entry.imageUrl ? entry.imageUrl : null, userId: match.id }));
    } catch(e){
      res.writeHead(502, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ imageUrl: null, error: 'roblox_unreachable' }));
    }
    return;
  }

  if(url.pathname === '/roblox/verify'){
    const username = url.searchParams.get('username') || '';
    const code = url.searchParams.get('code') || '';
    try{
      const match = await robloxResolveUsername(username);
      if(!match){ res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ ok: false, reason: `Couldn't find a Roblox account named "${username}".` })); return; }
      const profileR = await fetchWithRetry(`https://users.roblox.com/v1/users/${match.id}`);
      const profileData = await profileR.json();
      const bio = profileData.description || '';
      if(!bio.includes(code)){ res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ ok: false, reason: "Didn't find that code in your bio yet. Make sure you saved it, then try again." })); return; }
      // Use Roblox's own canonical username (match.name), not whatever
      // casing the person happened to type - otherwise "CoolGuy" and
      // "coolguy" silently become two different accounts with separate
      // balances/inventories. The client is told this name back so it logs
      // in (and saves its session) under the same canonical string too.
      const canonicalUsername = match.name;
      const token = issueSessionToken(canonicalUsername);
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ ok: true, userId: match.id, username: canonicalUsername, token }));
    } catch(e){
      res.writeHead(502, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ ok: false, reason: "Couldn't reach Roblox right now — try again in a few seconds." }));
    }
    return;
  }

  // TEMPORARY — testing-only bypass matching the client's skip-verify button.
  // Issues a real session token with zero Roblox check. Gated behind
  // ENABLE_DEV_BYPASS (off by default) rather than reachable in production -
  // see the flag's definition near the top of this file. Still fully
  // removable later (Phase 3) once you're confident nothing depends on it.
  if(url.pathname === '/dev/skip-login'){
    if (!ENABLE_DEV_BYPASS) {
      res.writeHead(404, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ ok: false }));
      return;
    }
    const username = (url.searchParams.get('username') || '').slice(0, 40) || 'testuser';
    const token = issueSessionToken(username);
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ ok: true, token }));
    return;
  }

  if(url.pathname.startsWith('/assets/img/')){
    return serveImageAsset(url.pathname, res);
  }

  serveIndexHtml(req, res);
});

// Images used to be base64-embedded directly in index.html (see the ~99%
// of that file's size that used to be base64 image data before the egress
// audit that led to this). They're now separate files on disk instead,
// named by a hash of their own content - which means two things for free:
// identical images naturally collapse onto the same filename (no explicit
// dedup bookkeeping needed), and it's always safe to cache a given
// filename forever, since the *only* way its content could ever change is
// for it to get a new name.
const ASSET_IMG_DIR = path.join(__dirname, 'assets', 'img');
// Filenames are always exactly a hex hash + .png/.webp (see how they were
// generated) - this is the only thing ever allowed to reach fs.readFile
// below, so a request can never escape this directory via '..', absolute
// paths, or anything else.
const SAFE_ASSET_FILENAME = /^[a-f0-9]{16,64}\.(png|webp)$/;

function serveImageAsset(pathname, res) {
  const filename = decodeURIComponent(pathname.slice('/assets/img/'.length));
  if (!SAFE_ASSET_FILENAME.test(filename)) {
    res.writeHead(400, { 'Content-Type': 'text/plain' });
    res.end('Bad asset request.');
    return;
  }
  fs.readFile(path.join(ASSET_IMG_DIR, filename), (err, data) => {
    if (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      res.end('Not found.');
      return;
    }
    res.writeHead(200, {
      'Content-Type': filename.endsWith('.webp') ? 'image/webp' : 'image/png',
      // Safe to cache forever, unconditionally - see the comment above on
      // why a given filename's content can never change.
      'Cache-Control': 'public, max-age=31536000, immutable',
    });
    res.end(data);
  });
}

// index.html used to be tens of MB (every pet's artwork was base64-embedded
// directly in it - see the egress audit that led to both this and the
// separate /assets/img/ static files above). It's now a normal-sized file,
// but this caching/compression setup is still worth keeping: it costs
// nothing, and it means a refresh can come back as a ~0-byte 304 instead
// of re-sending the file at all.
//   - gzip further shrinks what's left (plain HTML/JS/CSS text now,
//     instead of mostly-incompressible base64 image data).
//   - An ETag (a hash of the file's own bytes) lets a browser that already
//     has this exact version just get back a 304 Not Modified with no body
//     at all, instead of re-downloading anything, on every refresh.
// Restarting the server (e.g. after deploying an updated index.html)
// naturally invalidates this cache and recomputes it fresh, so this can
// never serve stale content after a real deploy.
let cachedIndexGzip = null;
let cachedIndexRaw = null;
let cachedIndexEtag = null;

function loadIndexHtmlCache() {
  const indexPath = path.join(__dirname, 'index.html');
  const raw = fs.readFileSync(indexPath);
  cachedIndexRaw = raw;
  cachedIndexGzip = zlib.gzipSync(raw, { level: zlib.constants.Z_BEST_COMPRESSION });
  cachedIndexEtag = '"' + crypto.createHash('sha1').update(raw).digest('hex') + '"';
  console.log(`[boot] Cached index.html: ${raw.length.toLocaleString()} bytes raw -> ${cachedIndexGzip.length.toLocaleString()} bytes gzipped.`);
}

function serveIndexHtml(req, res) {
  try {
    if (!cachedIndexGzip) loadIndexHtmlCache(); // lazy fallback if boot-time load somehow didn't run yet
  } catch (err) {
    res.writeHead(500, { 'Content-Type': 'text/plain' });
    res.end('Could not load website.');
    return;
  }

  if (req.headers['if-none-match'] === cachedIndexEtag) {
    res.writeHead(304);
    res.end();
    return;
  }

  const acceptEncoding = req.headers['accept-encoding'] || '';
  const canGzip = acceptEncoding.includes('gzip');
  res.writeHead(200, {
    'Content-Type': 'text/html; charset=utf-8',
    'ETag': cachedIndexEtag,
    // max-age=0 + must-revalidate: the browser always checks back in with
    // the server (a cheap ETag check, see above) rather than assuming an
    // old copy is still fine - important since this file does change
    // across deploys, and we never want someone stuck looking at a stale
    // version just because a longer cache time hadn't expired yet.
    'Cache-Control': 'public, max-age=0, must-revalidate',
    ...(canGzip ? { 'Content-Encoding': 'gzip' } : {}),
  });
  res.end(canGzip ? cachedIndexGzip : cachedIndexRaw);
}

const wss = new WebSocketServer({ server });

const HEARTBEAT_INTERVAL_MS = 30000;
setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.isAlive === false) {
      // Didn't respond to the last ping - it's dead, but nothing would
      // otherwise have noticed (no clean close handshake ever arrives from
      // a connection that just silently dropped). terminate() forces the
      // 'close' event to fire, which runs the existing username/socket
      // cleanup below exactly the same as a normal disconnect would.
      ws.terminate();
      continue;
    }
    ws.isAlive = false;
    ws.ping();
  }
}, HEARTBEAT_INTERVAL_MS);

wss.on('connection', (ws) => {
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch (e) { return; }

    if (msg.type === 'login') {
      const username = String(msg.username || '').slice(0, 40);
      if (!username) return;
      if (!checkSessionToken(username, msg.token)) {
        send(ws, { type: 'login:fail', reason: 'Your session expired or is invalid — please log in again.' });
        return;
      }
      if (siteLockdown && username !== ADMIN_USERNAME) {
        send(ws, { type: 'login:fail', reason: '🔒 The site is temporarily locked down for maintenance. Please try again later.' });
        return;
      }
      socketToUsername.set(ws, username);
      usernameToSocket.set(username, ws);
      const u = ensureUser(username);
      const myPendingWithdrawals = withdrawRequests
        .filter((r) => r.username === username && r.status === 'pending')
        .map((r) => ({ id: r.id, items: r.items, requestedAt: r.requestedAt }));
      send(ws, {
        type: 'login:ok',
        user: {
          username, coins: u.coins, inventory: u.inventory, stats: u.stats,
          specialRole: u.specialRole || null, mutedUntil: u.mutedUntil || 0,
          lockedItems: lockedItemsForUser(username),
          pendingWithdrawals: myPendingWithdrawals,
        },
      });
      send(ws, { type: 'exchange:stock', stock: shopStock });
      db.loadCoinflipHistoryForUser(username, 10).then((history) => {
        send(ws, { type: 'coinflip:history', history });
      }).catch((err) => console.error(`[db] Failed to load coinflip history for ${username}:`, err.message));
      send(ws, { type: 'coinflip:lobbies', lobbies: cfLobbies.map((l) => ({ id: l.id, creator: l.creator, side: l.side, items: l.items })) });
      send(ws, { type: 'diceduel:list', duels: diceDuelPublicList() });
      send(ws, { type: 'jackpot:state', ...jackpotPublicState() });
      send(ws, { type: 'sink:state', ...sinkPublicState(sinkRound) });
      send(ws, { type: 'rain:state', ...rainPublicState() });
      send(ws, { type: 'feed:recent', entries: liveFeed });
      send(ws, { type: 'chat:history', messages: chatHistory });
      const myMinesRound = activeMinesRounds.get(username);
      if (myMinesRound) {
        // Rebuilds the board on the client exactly where it left off -
        // the round itself already survives a refresh fine (it's keyed by
        // username in server memory, not tied to the socket), but without
        // this the client has no way to know it exists, tries to start a
        // fresh one, and just gets stuck on "you already have an active
        // round" with nothing to actually click. Bomb positions are never
        // sent, same as at every other point in a live round - only which
        // tiles are already safely revealed.
        const resumeMultiplier = minesMultiplier(myMinesRound.n, myMinesRound.mCount, myMinesRound.picks);
        send(ws, {
          type: 'mines:resume',
          n: myMinesRound.n, mCount: myMinesRound.mCount, gridSize: myMinesRound.gridSize,
          amount: myMinesRound.amount, picks: myMinesRound.picks,
          revealed: [...myMinesRound.revealed],
          multiplier: resumeMultiplier,
          payout: Math.floor(myMinesRound.amount * resumeMultiplier),
        });
      }
      broadcastBattlesTo(ws);
      if (username === ADMIN_USERNAME) {
        send(ws, { type: 'admin:withdrawList', requests: withdrawRequests.filter((r) => r.status === 'pending') });
      }
      return;
    }

    const username = socketToUsername.get(ws);
    if (!username) return; // must login first

    if (siteLockdown && username !== ADMIN_USERNAME && LOCKDOWN_BLOCKED_TYPES.has(msg.type)) {
      return send(ws, { type: 'error', message: '🔒 The site is temporarily locked down for maintenance. Please try again later.' });
    }

    switch (msg.type) {
      case 'rain:deposit': return handleRainDeposit(username, msg);
      case 'rain:claim': return handleRainClaim(username);
      case 'coinflip:create': return handleCoinflipCreate(username, msg);
      case 'coinflip:join': return handleCoinflipJoin(username, msg);
      case 'coinflip:cancel': return handleCoinflipCancel(username, msg);
      case 'diceduel:create': return handleDiceDuelCreate(username, msg);
      case 'diceduel:join': return handleDiceDuelJoin(username, msg);
      case 'diceduel:cancel': return handleDiceDuelCancel(username, msg);
      case 'jackpot:enter': return handleJackpotEnter(username, msg);
      case 'casebattle:create': return handleCaseBattleCreate(username, msg);
      case 'casebattle:join': return handleCaseBattleJoin(username, msg);
      case 'casebattle:start': return handleCaseBattleStart(username, msg);
      case 'casebattle:callBot': return handleCaseBattleCallBot(username, msg);
      case 'casebattle:cancel': return handleCaseBattleCancel(username, msg);
      case 'exchange:sell': return handleExchangeSell(username, msg);
      case 'exchange:buy': return handleExchangeBuy(username, msg);
      case 'account:reset': return handleAccountReset(username);
      case 'admin:lookup': return handleAdminLookup(username, msg);
      case 'admin:addCoins': return handleAdminAdjustCoins(username, msg, 1);
      case 'admin:removeCoins': return handleAdminAdjustCoins(username, msg, -1);
      case 'game:wager': return handleGameWager(username, msg);
      case 'game:resolve': return handleGameResolve(username, msg);
      case 'case:open': return handleCaseOpen(username, msg);
      case 'mines:start': return handleMinesStart(username, msg);
      case 'mines:reveal': return handleMinesReveal(username, msg);
      case 'mines:cashout': return handleMinesCashout(username);
      case 'sink:join': return handleSinkJoin(username, msg);
      case 'sink:cashout': return handleSinkCashout(username);
      case 'leaderboard:request': return handleLeaderboardRequest(username);
      case 'withdraw:request': return handleWithdrawRequest(username, msg);
      case 'withdraw:cancel': return handleWithdrawCancel(username, msg);
      case 'admin:withdrawList': return handleAdminWithdrawList(username);
      case 'admin:withdrawFulfill': return handleAdminWithdrawFulfill(username, msg);
      case 'admin:withdrawReject': return handleAdminWithdrawReject(username, msg);
      case 'chat:send': return handleChatSend(username, msg, ws);
      case 'tip:send': return handleTipSend(username, msg);
      case 'profile:request': return handleProfileRequest(username, msg);
      case 'admin:setRole': return handleAdminSetRole(username, msg);
    }
  });

  ws.on('close', () => {
    const username = socketToUsername.get(ws);
    socketToUsername.delete(ws);
    if (username && usernameToSocket.get(username) === ws) usernameToSocket.delete(username);
    // A duel that's still waiting for an opponent has only the creator's
    // items locked up, and only the creator was ever able to cancel it - if
    // they leave first, nothing else can free that escrow, so it's released
    // here instead of sitting locked forever. Once a 2nd player has joined
    // (status 'running'), rolls keep happening on the server's own timers
    // regardless of either connection - same as Case Battles already do -
    // so there's nothing to clean up there; the duel resolves and pays out
    // on schedule either way.
    if (username) {
      // Collected first rather than cancelled while iterating - nothing
      // stops someone from having more than one open duel at once (same as
      // Coinflip lobbies), and mutating the Map mid-iteration via delete()
      // inside cancelDiceDuelInternal isn't safe to do directly.
      const toCancel = [...diceDuels.values()].filter((d) => d.status === 'waiting' && d.creator === username);
      toCancel.forEach(cancelDiceDuelInternal);
    }
  });
});

function broadcastBattlesTo(ws) {
  send(ws, {
    type: 'casebattle:list',
    battles: [...battles.values()].map((b) => ({
      id: b.id, creator: b.creator, status: b.status, mode: b.mode,
      caseQueue: b.caseQueue, caseNames: b.caseNames,
      players: b.players.map((p) => ({ username: p.username, isBot: p.isBot, team: p.team, total: p.total || 0 })),
      winner: b.winner, winnerValue: b.winnerValue,
    })),
  });
}

const PORT = process.env.PORT || 8080;

// Boot sequence: schema first, then load every persisted user + their
// inventory into the in-memory `users` Map (same shape it's always had -
// nothing downstream needs to know this came from a database instead of
// starting empty), then pending withdrawal requests, and only THEN start
// accepting connections. If any of this fails, exit loudly rather than
// silently starting with an empty in-memory state that looks fine but
// quietly isn't backed by anything real.
(async () => {
  try {
    await db.initSchema();

    // One-time (but safe-to-repeat) cleanup: find any accounts that only
    // differ by capitalization (e.g. "DTN_bgsi" vs "DTN_BGSI" - created
    // before logins were normalized to Roblox's canonical username) and
    // merge them into the real canonical account. Runs every boot but is a
    // no-op once there's nothing left to merge, so it's safe to leave in
    // permanently rather than needing to remember to run it once and
    // remove it.
    try {
      const clusters = await db.findDuplicateCaseClusters();
      if (clusters.length) {
        console.log(`[boot] Found ${clusters.length} username cluster(s) differing only by capitalization - resolving canonical names via Roblox...`);
      }
      for (const cluster of clusters) {
        let canonical;
        try {
          const match = await robloxResolveUsername(cluster[0]);
          canonical = match ? match.name : null;
        } catch (err) {
          console.warn(`[boot] Couldn't reach Roblox to resolve canonical name for [${cluster.join(', ')}] - skipping this cluster for now, will retry next boot:`, err.message);
          continue;
        }
        if (!canonical) {
          console.warn(`[boot] Roblox has no account matching [${cluster.join(', ')}] anymore (renamed/deleted?) - leaving these accounts separate, review manually if needed.`);
          continue;
        }
        try {
          const result = await db.mergeCasedDuplicates(canonical, cluster);
          if (result) {
            console.log(`[boot] Merged [${result.mergedFrom.join(', ')}] into "${result.canonicalUsername}" - final balance ${result.coins} coins, ${result.itemCount} distinct item(s).`);
          }
        } catch (err) {
          console.error(`[boot] Failed to merge cluster [${cluster.join(', ')}]:`, err.message);
        }
      }
    } catch (err) {
      console.error('[boot] Duplicate-account check failed (continuing to boot normally):', err.message);
    }

    const loadedUsers = await db.loadAllUsers();
    for (const [uname, u] of loadedUsers) users.set(uname, u);
    console.log(`[boot] Loaded ${loadedUsers.size} user account(s) from Postgres.`);

    const loadedRequests = await db.loadPendingWithdrawRequests();
    withdrawRequests = loadedRequests;
    console.log(`[boot] Loaded ${loadedRequests.length} pending withdrawal request(s) from Postgres.`);

    const loadedCfLobbies = await db.loadPendingCoinflipLobbies();
    cfLobbies = loadedCfLobbies;
    console.log(`[boot] Loaded ${loadedCfLobbies.length} pending coinflip lobby(ies) from Postgres.`);

    loadIndexHtmlCache();
    startSinkJoiningPhase();
    server.listen(PORT, () => console.log(`BloxyVault server listening on :${PORT}`));
  } catch (err) {
    console.error('[boot] Failed to start - could not initialize/load from Postgres:', err);
    process.exit(1);
  }
})();

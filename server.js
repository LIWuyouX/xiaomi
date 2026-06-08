const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = 3456;
const CARDS_PER_PLAYER = 4;
const INITIAL_PEEKS = 2;
const TOTAL_ROUNDS = 4;

// ═══ Helpers ═══

function createDeck() {
  const deck = [];
  for (let v = 0; v <= 13; v++) {
    for (let i = 0; i < 4; i++) deck.push(v);
  }
  return deck;
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function powerType(val) {
  if (val === 7 || val === 8) return 'peek';
  if (val === 9 || val === 10) return 'spy';
  if (val === 11 || val === 12) return 'swap';
  return null;
}

// ═══ Game Class ═══

class CaboGame {
  constructor(totalPlayers) {
    this.totalSlots = totalPlayers;
    this.players = [];
    this.deck = [];
    this.discardPile = [];
    this.currentPlayer = 0;
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.caboCaller = null;
    this.caboExtraTurns = [];
    this.phase = 'lobby';
    this.round = 1;
    this.logMessages = [];
    this.pendingAction = null;
    this.powerJustUsed = false;
    this.startingPlayer = 0;
    this.scoringResults = null;
    this._peekClearTimers = {};
  }

  get currentPlayerObj() {
    return this.players[this.currentPlayer];
  }

  // ── Player state ──
  replaceSlot(slotId, playerName, isHuman) {
    if (!this.players[slotId]) {
      this.players[slotId] = {
        id: slotId, name: playerName, isHuman,
        cards: [], known: [], publicKnown: [],
        totalScore: 0, roundScore: 0, peekCount: 0, aiMemory: {},
      };
    } else {
      this.players[slotId].name = playerName;
      this.players[slotId].isHuman = isHuman;
    }
  }

  // ── Build state for a given player ──
  getState(playerId) {
    const me = this.players[playerId];
    let humanPeeksRemaining = 0;
    if (this.phase === 'peeking' && me && me.isHuman) {
      humanPeeksRemaining = Math.max(0, INITIAL_PEEKS - (me.peekCount || 0));
    }
    return {
      phase: this.phase,
      round: this.round,
      currentPlayer: this.currentPlayer,
      players: this.players.map(p => ({
        id: p.id, name: p.name, isHuman: p.isHuman,
        cardCount: p.cards.length,
        totalScore: p.totalScore, roundScore: p.roundScore,
        known: playerId === p.id ? p.known.slice() : [],
        publicKnown: p.publicKnown.slice(),
      })),
      yourId: playerId,
      deckCount: this.deck.length,
      discardPile: [...this.discardPile],
      topDiscard: this.discardPile.length > 0 ? this.discardPile[this.discardPile.length - 1] : null,
      drawnCard: playerId === this.currentPlayer ? this.drawnCard : null,
      matchingCards: playerId === this.currentPlayer ? this.getMatches() : [],
      pendingAction: playerId === this.currentPlayer ? this.pendingAction : null,
      powerJustUsed: this.powerJustUsed,
      caboCaller: this.caboCaller,
      scoringResults: this.scoringResults ? this.scoringResults.map(r => ({
        playerId: r.player.id, name: r.player.name, isHuman: r.player.isHuman,
        cards: r.cards, sum: r.sum, bonus: r.bonus || null,
        roundScore: r.player.roundScore, totalScore: r.player.totalScore,
      })) : null,
      logMessages: [...this.logMessages],
      humanPeeksRemaining,
      totalSlots: this.totalSlots,
    };
  }

  // ── Get matches between drawn card and known player cards ──
  getMatches() {
    if (this.drawnCard === null) return [];
    const player = this.currentPlayerObj;
    const matches = [];
    for (let i = 0; i < player.cards.length; i++) {
      if (player.known[i] !== null && player.known[i] === this.drawnCard) {
        matches.push(i);
      }
    }
    return matches;
  }

  // ── Single match (顶一张已知的) ──
  matchCard(cardIndex) {
    if (this.drawnCard === null) return false;
    const player = this.currentPlayerObj;
    if (player.known[cardIndex] !== this.drawnCard) return false;
    const matchedVal = this.drawnCard;
    player.cards.splice(cardIndex, 1);
    player.known.splice(cardIndex, 1);
    player.publicKnown.splice(cardIndex, 1);
    this.discardPile.push(matchedVal);
    this.discardPile.push(matchedVal);
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.log(player.name + ' 顶出了 ' + matchedVal + '！两张弃掉，剩 ' + player.cards.length + ' 张');
    this.finishAction();
    return true;
  }

  // ── Multi-match (顶多张) ──
  startMultiMatch() {
    if (this.drawnCard === null) return false;
    this.pendingAction = { type: 'multi_match', selected: [] };
    return true;
  }

  toggleMultiSelect(cardIndex) {
    if (!this.pendingAction || this.pendingAction.type !== 'multi_match') return;
    const sel = this.pendingAction.selected;
    const idx = sel.indexOf(cardIndex);
    if (idx >= 0) sel.splice(idx, 1);
    else sel.push(cardIndex);
  }

  confirmMultiMatch() {
    if (!this.pendingAction || this.pendingAction.type !== 'multi_match') return false;
    const selected = [...this.pendingAction.selected];
    const player = this.currentPlayerObj;
    const drawnVal = this.drawnCard;

    if (selected.length === 0) return false;

    // Check if ALL selected cards have the SAME value (match each other)
    const firstVal = player.cards[selected[0]];
    const allSame = selected.every(i => player.cards[i] === firstVal);

    if (allSame) {
      // Success: discard selected cards, drawn card goes to hand face-down
      for (const i of selected.sort((a, b) => b - a)) {
        this.discardPile.push(player.cards[i]);
        player.cards.splice(i, 1);
        player.known.splice(i, 1);
        player.publicKnown.splice(i, 1);
      }
      // Drawn card added to hand (private)
      player.cards.push(drawnVal);
      player.known.push(drawnVal);
      player.publicKnown.push(null);
      this.log(player.name + ' 用 ' + drawnVal + ' 顶出 ' + selected.length + ' 张 ' + firstVal + '！剩 ' + player.cards.length + ' 张');
    } else {
      // Fail: drawn card added to hand face-up, selected cards revealed
      player.cards.push(drawnVal);
      player.known.push(drawnVal);
      player.publicKnown.push(drawnVal); // drawn card becomes public
      for (const i of selected) {
        player.known[i] = player.cards[i];
        player.publicKnown[i] = player.cards[i];
      }
      this.log(player.name + ' 顶牌失败！牌被亮出，新增一张 ' + drawnVal + '（共 ' + player.cards.length + ' 张）');
    }

    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.pendingAction = null;
    this.finishAction();
    return true;
  }

  // ── Round setup ──
  startRound() {
    this.deck = shuffle(createDeck());
    this.discardPile = [];
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.caboCaller = null;
    this.caboExtraTurns = [];
    this.phase = 'setup';
    this.pendingAction = null;
    this.powerJustUsed = false;
    this.scoringResults = null;
    this._peekClearTimers = {};

    for (const p of this.players) {
      p.cards = [];
      p.known = [];
      p.publicKnown = [];
      p.roundScore = 0;
      p.peekCount = 0;
      for (let i = 0; i < CARDS_PER_PLAYER; i++) {
        p.cards.push(this.deck.pop());
        p.known.push(null);
        p.publicKnown.push(null);
      }
      if (!p.isHuman) {
        p.aiMemory = {};
        for (const other of this.players) {
          if (other.id !== p.id) {
            p.aiMemory[other.id] = [];
            for (let j = 0; j < CARDS_PER_PLAYER; j++) p.aiMemory[other.id].push(null);
          }
        }
      }
    }

    this.discardPile.push(this.deck.pop());
    this.currentPlayer = this.startingPlayer;
    this.startingPlayer = (this.startingPlayer + 1) % this.totalSlots;
    this.phase = 'peeking';
    this.log('新一轮开始！每位玩家可偷看 ' + INITIAL_PEEKS + ' 张牌（2秒后隐藏）。');
    this.aiPeekAll();
  }

  // ── AI peeking (AI remembers permanently) ──
  aiPeekAll() {
    for (const p of this.players) {
      if (p.isHuman) continue;
      const unknown = p.known.map((k, i) => k === null ? i : -1).filter(i => i >= 0);
      shuffle(unknown);
      const toPeek = unknown.slice(0, INITIAL_PEEKS);
      for (const idx of toPeek) {
        p.known[idx] = p.cards[idx];
      }
      p.peekCount = INITIAL_PEEKS;
    }
    if (this.allHumansPeeked()) {
      this.phase = 'playing';
      this.log('游戏开始！轮到 ' + this.currentPlayerObj.name + '。');
    }
  }

  allHumansPeeked() {
    for (const p of this.players) {
      if (!p.isHuman) continue;
      if ((p.peekCount || 0) < INITIAL_PEEKS) return false;
    }
    return true;
  }

  humanPeek(playerId, cardIndex) {
    if (this.phase !== 'peeking') return false;
    const player = this.players[playerId];
    if (!player || !player.isHuman) return false;
    if ((player.peekCount || 0) >= INITIAL_PEEKS) return false;

    player.peekCount = (player.peekCount || 0) + 1;
    player.known[cardIndex] = player.cards[cardIndex];
    this.log(player.name + ' 查看了第 ' + (cardIndex + 1) + ' 张牌（2秒后隐藏）');

    if (this.allHumansPeeked()) {
      this.phase = 'playing';
      this.log('游戏开始！轮到 ' + this.currentPlayerObj.name + '。');
    }
    return player.cards[cardIndex]; // return value for timeout handling
  }

  // ── Draw / Take discard ──
  drawCard() {
    if (this.deck.length === 0) {
      this.reshuffleDiscard();
      if (this.deck.length === 0) { this.endRound(); return; }
    }
    this.drawnCard = this.deck.pop();
    this.drawnFromDiscard = false;
    this.log(this.currentPlayerObj.name + ' 从牌堆抽了一张牌。');
  }

  takeFromDiscard() {
    if (this.discardPile.length === 0) return false;
    this.drawnCard = this.discardPile.pop();
    this.drawnFromDiscard = true;
    this.log(this.currentPlayerObj.name + ' 从弃牌堆拿了 ' + this.drawnCard + '。');
    return true;
  }

  reshuffleDiscard() {
    if (this.discardPile.length <= 1) return;
    const top = this.discardPile.pop();
    const rest = shuffle([...this.discardPile]);
    this.deck.push(...rest);
    this.discardPile = [top];
    this.log('弃牌堆已重新洗入牌堆。');
  }

  // ── Swap drawn with own card ──
  swapWithOwn(cardIndex) {
    if (this.drawnCard === null) return false;
    const player = this.currentPlayerObj;
    const oldCard = player.cards[cardIndex];
    player.cards[cardIndex] = this.drawnCard;
    player.known[cardIndex] = this.drawnCard;
    this.discardPile.push(oldCard);
    this.log(player.name + ' 替换了第 ' + (cardIndex + 1) + ' 张牌（弃掉 ' + oldCard + '）。');
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.finishAction();
    return true;
  }

  // ── Use power card ──
  usePower() {
    if (this.drawnCard === null) return false;
    if (this.drawnFromDiscard) return false;
    const power = powerType(this.drawnCard);
    if (!power) return false;

    this.discardPile.push(this.drawnCard);
    const val = this.drawnCard;
    this.drawnCard = null;
    this.log(this.currentPlayerObj.name + ' 弃掉 ' + val + ' 并使用能力。');

    if (this.currentPlayerObj.isHuman) {
      this.pendingAction = { type: power, val: val };
      this.powerJustUsed = true;
      return true;
    } else {
      this.aiUsePower(power);
      this.finishAction();
      return true;
    }
  }

  // ── Human power target selection ──
  humanPowerTarget(target) {
    if (!this.pendingAction) return false;
    const action = this.pendingAction;
    const player = this.currentPlayerObj;

    if (action.type === 'peek') {
      const idx = target.cardIndex;
      if (player.known[idx] !== null) return false;
      player.known[idx] = player.cards[idx];
      this.log(player.name + ' 查看了自己的第 ' + (idx + 1) + ' 张牌（2秒后隐藏）');
      return { type: 'peek', playerId: player.id, cardIndex: idx };
    } else if (action.type === 'spy') {
      const opp = this.players[target.playerId];
      const val = opp.cards[target.cardIndex];
      opp.publicKnown[target.cardIndex] = val;
      this.log(player.name + ' 偷看了 ' + opp.name + ' 的一张牌');
      return { type: 'spy', playerId: opp.id, cardIndex: target.cardIndex };
    } else if (action.type === 'swap') {
      const opp = this.players[target.playerId];
      const myIdx = target.myCardIndex;
      const theirIdx = target.theirCardIndex;
      [player.cards[myIdx], opp.cards[theirIdx]] = [opp.cards[theirIdx], player.cards[myIdx]];
      player.known[myIdx] = null;
      opp.known[theirIdx] = null;
      player.publicKnown[myIdx] = null;
      opp.publicKnown[theirIdx] = null;
      for (const p of this.players) {
        if (!p.isHuman) {
          if (p.aiMemory[opp.id]) p.aiMemory[opp.id][theirIdx] = null;
          if (p.aiMemory[player.id]) p.aiMemory[player.id][myIdx] = null;
        }
      }
      this.log(player.name + ' 与 ' + opp.name + ' 交换了一张牌');
    }

    this.pendingAction = null;
    this.powerJustUsed = false;
    this.finishAction();
    return true;
  }

  // ── Cabo ──
  callCabo() {
    if (this.drawnCard !== null) return false;
    this.caboCaller = this.currentPlayer;
    this.log('🚨 ' + this.currentPlayerObj.name + ' 喊了 CABO！');
    this.phase = 'cabo_extra';
    this.caboExtraTurns = [];
    for (let i = 0; i < this.players.length; i++) {
      if (i !== this.currentPlayer) this.caboExtraTurns.push(i);
    }
    this.advanceCaboExtraTurn();
  }

  advanceCaboExtraTurn() {
    if (this.caboExtraTurns.length === 0) { this.endRound(); return; }
    this.currentPlayer = this.caboExtraTurns.shift();
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.pendingAction = null;
    this.powerJustUsed = false;
    this.log('CABO 额外回合 - 轮到 ' + this.currentPlayerObj.name + '。');
  }

  finishAction() {
    if (this.phase === 'cabo_extra') { this.advanceCaboExtraTurn(); return; }
    this.currentPlayer = (this.currentPlayer + 1) % this.totalSlots;
    this.drawnCard = null;
    this.drawnFromDiscard = false;
    this.pendingAction = null;
    this.powerJustUsed = false;
  }

  // ── Scoring ──
  endRound() {
    this.phase = 'scoring';
    this.log('━━━ 本回合结束，亮牌计分！━━━');
    const scores = this.players.map(p => ({
      player: p, sum: p.cards.reduce((a, b) => a + b, 0), cards: [...p.cards],
    }));
    const minSum = Math.min(...scores.map(s => s.sum));
    for (const s of scores) {
      let pts = s.sum;
      if (this.caboCaller !== null && s.player.id === this.caboCaller) {
        if (s.sum === minSum) { pts = 0; s.bonus = 'best'; }
        else { pts = s.sum + 10; s.bonus = 'penalty'; }
      }
      s.player.roundScore = pts;
      s.player.totalScore += pts;
    }
    this.scoringResults = scores;
    if (this.round >= TOTAL_ROUNDS) { this.phase = 'gameOver'; this.log('━━━ 游戏结束！━━━'); }
  }

  startNextRound() {
    if (this.phase === 'gameOver') {
      for (const p of this.players) { p.totalScore = 0; p.roundScore = 0; }
      this.round = 1; this.startingPlayer = 0;
    } else { this.round++; }
    this.scoringResults = null;
    this.startRound();
  }

  // ── AI Logic ──
  aiShouldCallCabo(ai) {
    const knownSum = ai.known.filter(k => k !== null).reduce((a, b) => a + b, 0);
    const unknownCount = ai.known.filter(k => k === null).length;
    if (unknownCount === 0 && knownSum <= 6) return true;
    if (knownSum + unknownCount * 6.5 <= 8 && unknownCount <= 1) return true;
    return false;
  }

  aiTakeTurn(isCaboExtra = false) {
    const ai = this.currentPlayerObj;
    if (ai.isHuman) return;

    if (!isCaboExtra && this.drawnCard === null && this.caboCaller === null) {
      if (this.aiShouldCallCabo(ai)) { this.callCabo(); return; }
    }

    const topDiscard = this.discardPile.length > 0 ? this.discardPile[this.discardPile.length - 1] : null;
    let tookDiscard = false;
    if (topDiscard !== null && topDiscard <= 3) { this.takeFromDiscard(); tookDiscard = true; }
    else { this.drawCard(); }

    // Check single match
    const matches = this.getMatches();
    if (matches.length > 0) { this.matchCard(matches[0]); return; }

    const power = powerType(this.drawnCard);
    const drawnVal = this.drawnCard;
    const knownCards = ai.known.map((k, i) => ({ val: k, idx: i }));
    const unknownCount = knownCards.filter(k => k.val === null).length;
    const knownSum = knownCards.filter(k => k.val !== null).reduce((s, k) => s + k.val, 0);

    let shouldSwap = false, swapTarget = -1;
    const knownHigh = knownCards.filter(k => k.val !== null).sort((a, b) => b.val - a.val);
    if (knownHigh.length > 0 && knownHigh[0].val > drawnVal) {
      shouldSwap = true; swapTarget = knownHigh[0].idx;
    } else if (unknownCount > 0 && knownSum + unknownCount * 6.5 > 20) {
      shouldSwap = true; swapTarget = knownCards.find(k => k.val === null).idx;
    }

    if (power && !tookDiscard && !shouldSwap) { this.usePower(); return; }
    if (shouldSwap && swapTarget >= 0) { this.swapWithOwn(swapTarget); }
    else {
      this.discardPile.push(this.drawnCard);
      this.log(ai.name + ' 弃掉了 ' + this.drawnCard + '。');
      this.drawnCard = null;
      this.drawnFromDiscard = false;
      this.finishAction();
    }
  }

  aiUsePower(power) {
    const ai = this.currentPlayerObj;
    if (power === 'peek') {
      const unknown = ai.known.map((k, i) => k === null ? i : -1).filter(i => i >= 0);
      if (unknown.length > 0) {
        const idx = unknown[Math.floor(Math.random() * unknown.length)];
        ai.known[idx] = ai.cards[idx];
        this.log(ai.name + ' 查看了自己的一张牌。');
      }
    } else if (power === 'spy') {
      const opponents = this.players.filter(p => p.id !== ai.id && p.isHuman);
      if (opponents.length > 0) {
        const opp = opponents[Math.floor(Math.random() * opponents.length)];
        const idx = Math.floor(Math.random() * opp.cards.length);
        ai.aiMemory[opp.id] = ai.aiMemory[opp.id] || [];
        while (ai.aiMemory[opp.id].length < opp.cards.length) ai.aiMemory[opp.id].push(null);
        ai.aiMemory[opp.id][idx] = opp.cards[idx];
        this.log(ai.name + ' 偷看了 ' + opp.name + ' 的一张牌。');
      }
    } else if (power === 'swap') {
      const knownHigh = ai.known.map((k, i) => ({ val: k, idx: i }))
        .filter(x => x.val !== null && x.val >= 8).sort((a, b) => a.val - b.val);
      if (knownHigh.length > 0) {
        const myIdx = knownHigh[0].idx;
        const opponents = this.players.filter(p => p.id !== ai.id);
        if (opponents.length > 0) {
          const opp = opponents[Math.floor(Math.random() * opponents.length)];
          const theirIdx = Math.floor(Math.random() * opp.cards.length);
          [ai.cards[myIdx], opp.cards[theirIdx]] = [opp.cards[theirIdx], ai.cards[myIdx]];
          ai.known[myIdx] = null; opp.known[theirIdx] = null;
          for (const p of this.players) {
            if (!p.isHuman) {
              if (p.aiMemory[opp.id]) p.aiMemory[opp.id][theirIdx] = null;
              if (p.aiMemory[ai.id]) p.aiMemory[ai.id][myIdx] = null;
            }
          }
          this.log(ai.name + ' 与 ' + opp.name + ' 交换了一张牌！');
        }
      }
    }
  }

  log(msg) {
    this.logMessages.push(msg);
    if (this.logMessages.length > 50) this.logMessages.shift();
  }
}

// ═══ Room Manager ═══

const rooms = new Map();

function randomCode() { return String(Math.floor(1000 + Math.random() * 9000)); }

function broadcast(room, stateFn) {
  for (const [pid, ws] of room.clients) {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({ type: 'game_state', state: stateFn(pid) }));
    }
  }
}

function scheduleAI(room) {
  if (room._aiTimeout) clearTimeout(room._aiTimeout);
  const game = room.game;
  const cur = game.currentPlayerObj;
  if (cur && !cur.isHuman && (game.phase === 'playing' || game.phase === 'cabo_extra') && game.pendingAction === null) {
    room._aiTimeout = setTimeout(() => {
      game.aiTakeTurn(game.phase === 'cabo_extra');
      broadcast(room, pid => game.getState(pid));
      scheduleAI(room);
    }, 800);
  }
}

// Clear peek reveal after 2 seconds
function schedulePeekClear(room, playerId, cardIndex) {
  const key = playerId + '_' + cardIndex;
  if (room._peekTimers && room._peekTimers[key]) clearTimeout(room._peekTimers[key]);
  if (!room._peekTimers) room._peekTimers = {};
  room._peekTimers[key] = setTimeout(() => {
    const p = room.game.players[playerId];
    if (p && p.known[cardIndex] !== null) {
      p.known[cardIndex] = null;
      broadcast(room, pid => room.game.getState(pid));
    }
    delete room._peekTimers[key];
  }, 2000);
}

function scheduleSpyClear(room, playerId, cardIndex) {
  const key = 'spy_' + playerId + '_' + cardIndex;
  if (room._spyTimers && room._spyTimers[key]) clearTimeout(room._spyTimers[key]);
  if (!room._spyTimers) room._spyTimers = {};
  room._spyTimers[key] = setTimeout(() => {
    const p = room.game.players[playerId];
    if (p && p.publicKnown[cardIndex] !== null) {
      p.publicKnown[cardIndex] = null;
      broadcast(room, pid => room.game.getState(pid));
    }
    delete room._spyTimers[key];
  }, 3000);
}

// ═══ HTTP Server ═══

const server = http.createServer((req, res) => {
  if (req.url === '/' || req.url === '/cabo.html') {
    fs.readFile(path.join(__dirname, 'cabo.html'), (err, data) => {
      if (err) { res.writeHead(500); res.end('Error'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(data);
    });
  } else { res.writeHead(404); res.end('Not found'); }
});

// ═══ WebSocket ═══

const wss = new WebSocketServer({ server });

wss.on('connection', (ws) => {
  let session = null;

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch (e) { return; }

    switch (msg.type) {

      case 'create_room': {
        const code = randomCode();
        const total = Math.min(4, Math.max(2, msg.totalPlayers || 3));
        const fillAI = msg.fillAI !== false;
        const game = new CaboGame(total);
        game.replaceSlot(0, msg.playerName, true);
        if (fillAI) {
          for (let i = 1; i < total; i++) game.replaceSlot(i, '电脑' + String.fromCharCode(64 + i), false);
        }
        const room = { game, clients: new Map(), totalSlots: total, fillAI };
        room.clients.set(0, ws);
        rooms.set(code, room);
        session = { roomCode: code, playerId: 0 };
        ws.send(JSON.stringify({ type: 'room_created', roomCode: code, playerId: 0, totalSlots: total, fillAI }));
        ws.send(JSON.stringify({ type: 'game_state', state: game.getState(0) }));
        break;
      }

      case 'join_room': {
        const room = rooms.get(msg.roomCode);
        if (!room) { ws.send(JSON.stringify({ type: 'error', message: '房间不存在' })); return; }
        if (room.game.phase !== 'lobby') { ws.send(JSON.stringify({ type: 'error', message: '游戏已开始' })); return; }
        let slotId = -1;
        for (let i = 0; i < room.totalSlots; i++) {
          if (!room.clients.has(i)) { slotId = i; break; }
        }
        if (slotId === -1) { ws.send(JSON.stringify({ type: 'error', message: '房间已满' })); return; }
        room.game.replaceSlot(slotId, msg.playerName, true);
        room.clients.set(slotId, ws);
        session = { roomCode: msg.roomCode, playerId: slotId };
        ws.send(JSON.stringify({ type: 'room_joined', playerId: slotId, totalSlots: room.totalSlots }));
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'start_game': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        const humanCount = room.game.players.filter(p => p.isHuman).length;
        if (humanCount < 2) { ws.send(JSON.stringify({ type: 'error', message: '至少需要2名玩家' })); return; }
        if (room.fillAI !== false) {
          for (let i = 0; i < room.totalSlots; i++) {
            if (!room.clients.has(i) && (!room.game.players[i] || !room.game.players[i].isHuman)) {
              room.game.replaceSlot(i, '电脑' + String.fromCharCode(64 + i), false);
            }
          }
        } else {
          room.game.players = room.game.players.filter(p => p && p.name);
          room.game.totalSlots = room.game.players.length;
          room.totalSlots = room.game.players.length;
        }
        room.game.startRound();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'peek': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        const val = room.game.humanPeek(session.playerId, msg.cardIndex);
        if (val === false) { ws.send(JSON.stringify({ type: 'error', message: '无法查看' })); return; }
        broadcast(room, pid => room.game.getState(pid));
        schedulePeekClear(room, session.playerId, msg.cardIndex);
        scheduleAI(room);
        break;
      }

      case 'draw': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard !== null) return;
        room.game.drawCard();
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'take_discard': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard !== null) return;
        room.game.takeFromDiscard();
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'swap_own': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard === null) return;
        room.game.swapWithOwn(msg.cardIndex);
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'use_power': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard === null) return;
        room.game.usePower();
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'power_target': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        const result = room.game.humanPowerTarget(msg);
        broadcast(room, pid => room.game.getState(pid));
        if (result && result.type === 'peek') schedulePeekClear(room, result.playerId, result.cardIndex);
        if (result && result.type === 'spy') scheduleSpyClear(room, result.playerId, result.cardIndex);
        scheduleAI(room);
        break;
      }

      case 'discard_drawn': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard === null) return;
        room.game.discardPile.push(room.game.drawnCard);
        room.game.log(room.game.currentPlayerObj.name + ' 弃掉了 ' + room.game.drawnCard + '。');
        room.game.drawnCard = null;
        room.game.drawnFromDiscard = false;
        room.game.finishAction();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'call_cabo': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard !== null) return;
        room.game.callCabo();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'match': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard === null) return;
        room.game.matchCard(msg.cardIndex);
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'multi_start': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.drawnCard === null) return;
        room.game.startMultiMatch();
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'multi_toggle': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        room.game.toggleMultiSelect(msg.cardIndex);
        broadcast(room, pid => room.game.getState(pid));
        break;
      }

      case 'multi_confirm': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        room.game.confirmMultiMatch();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'next_round': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (room.game.phase !== 'scoring') return;
        room.game.startNextRound();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'new_game': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (room.game.phase !== 'gameOver') return;
        room.game.startNextRound();
        broadcast(room, pid => room.game.getState(pid));
        scheduleAI(room);
        break;
      }

      case 'cancel_power': {
        const room = rooms.get(session.roomCode);
        if (!room) return;
        if (session.playerId !== room.game.currentPlayer) return;
        if (room.game.powerJustUsed) {
          room.game.pendingAction = null;
          room.game.powerJustUsed = false;
          room.game.finishAction();
          broadcast(room, pid => room.game.getState(pid));
          scheduleAI(room);
        } else {
          room.game.pendingAction = null;
          room.game.powerJustUsed = false;
          broadcast(room, pid => room.game.getState(pid));
        }
        break;
      }
    }
  });

  ws.on('close', () => {
    if (session) {
      const room = rooms.get(session.roomCode);
      if (room) {
        room.clients.delete(session.playerId);
        if (room.clients.size === 0) rooms.delete(session.roomCode);
        else broadcast(room, pid => room.game.getState(pid));
      }
    }
  });
});

server.listen(PORT, () => {
  console.log('🃏 Cabo 联机服务器已启动');
  console.log('   本地: http://localhost:' + PORT);
});

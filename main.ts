import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Four moves: [dRow, dCol, letter]. Fixed order everywhere = deterministic.
const DIRS = [[-1, 0, 'u'], [1, 0, 'd'], [0, -1, 'l'], [0, 1, 'r']];

function parse(level) {
  const rows = level.split('\n');
  while (rows.length && rows[rows.length - 1] === '') rows.pop();
  const H = rows.length;
  const W = Math.max(...rows.map(r => r.length));
  const N = W * H;
  const wall = new Uint8Array(N);
  const goals = new Set();
  const boxes = [];
  let player = -1;
  for (let r = 0; r < H; r++) {
    for (let c = 0; c < W; c++) {
      const ch = rows[r][c] ?? ' ';
      const i = r * W + c;
      if (ch === '#') wall[i] = 1;
      else {
        if (ch === '.' || ch === '*' || ch === '+') goals.add(i);
        if (ch === '$' || ch === '*') boxes.push(i);
        if (ch === '@' || ch === '+') player = i;
      }
    }
  }
  return { W, H, N, wall, goals, boxes, player };
}

// Live squares: a floor square is live when a box there can still reach a
// goal by pushes (walls only). Pull-back from the goals: square s is live
// when some neighbour s+d is live and s-d is floor (room for the player
// to stand and push s towards s+d). Never prunes a solvable state.
function liveSquares(wall, goals, W, H) {
  const live = new Set(goals);
  let changed = true;
  while (changed) {
    changed = false;
    for (let r = 0; r < H; r++) {
      for (let c = 0; c < W; c++) {
        const i = r * W + c;
        if (wall[i] || live.has(i)) continue;
        for (const [dr, dc] of DIRS) {
          const tr = r + dr, tc = c + dc, ur = r - dr, uc = c - dc;
          if (tr < 0 || tr >= H || tc < 0 || tc >= W) continue;
          if (ur < 0 || ur >= H || uc < 0 || uc >= W) continue;
          if (live.has(tr * W + tc) && !wall[ur * W + uc]) {
            live.add(i);
            changed = true;
            break;
          }
        }
      }
    }
  }
  return live;
}

// All floor squares in `cells` reachable on foot from `start`, boxes as
// obstacles. Returns the set of reachable squares.
function reach(start, boxSet, cells, W, H) {
  const seen = new Set([start]);
  const q = [start];
  for (let h = 0; h < q.length; h++) {
    const cur = q[h];
    const r = Math.floor(cur / W), c = cur % W;
    for (const [dr, dc] of DIRS) {
      const nr = r + dr, nc = c + dc;
      if (nr < 0 || nr >= H || nc < 0 || nc >= W) continue;
      const ni = nr * W + nc;
      if (!cells.has(ni) || boxSet.has(ni) || seen.has(ni)) continue;
      seen.add(ni);
      q.push(ni);
    }
  }
  return seen;
}

// Shortest walk (BFS, fixed direction order) from `from` to `to` over
// `cells`, boxes as obstacles. Returns the move string, or null.
function walkPath(from, to, boxSet, cells, W, H) {
  if (from === to) return '';
  const prev = new Map([[from, null]]);
  const q = [from];
  for (let h = 0; h < q.length; h++) {
    const cur = q[h];
    const r = Math.floor(cur / W), c = cur % W;
    for (const [dr, dc, ch] of DIRS) {
      const nr = r + dr, nc = c + dc;
      if (nr < 0 || nr >= H || nc < 0 || nc >= W) continue;
      const ni = nr * W + nc;
      if (!cells.has(ni) || boxSet.has(ni) || prev.has(ni)) continue;
      prev.set(ni, [cur, ch]);
      if (ni === to) {
        let s = '';
        let n = ni;
        while (n !== from) {
          const [p, c2] = prev.get(n);
          s = c2 + s;
          n = p;
        }
        return s;
      }
      q.push(ni);
    }
  }
  return null;
}

// Push-optimal BFS for one room (or a whole level as fallback).
// State = sorted box squares + lowest square of the player's reachable
// region. Level-order expansion => first solved state is push-optimal.
// Returns { text, player, boxes } or null when the work cap is hit.
function solveRoom(cells, boxes0, goals, entry, live, W, H) {
  const startBoxes = [...boxes0].sort((a, b) => a - b);
  const solved = bs => bs.every(b => goals.has(b));
  if (solved(startBoxes)) return { text: '', player: entry, boxes: startBoxes };
  const keyOf = (bs, low) => bs.join(',') + '|' + low;
  const lowest = set => {
    let m = Infinity;
    for (const x of set) if (x < m) m = x;
    return m;
  };
  const startRegion = reach(entry, new Set(startBoxes), cells, W, H);
  const nodes = [{ boxes: startBoxes, player: entry, parent: -1, step: '' }];
  const seen = new Set([keyOf(startBoxes, lowest(startRegion))]);
  const q = [0];
  for (let h = 0; h < q.length; h++) {
    if (seen.size > 250000) return null;
    const ni = q[h];
    const node = nodes[ni];
    const boxSet = new Set(node.boxes);
    const region = reach(node.player, boxSet, cells, W, H);
    for (let bi = 0; bi < node.boxes.length; bi++) {
      const b = node.boxes[bi];
      const br = Math.floor(b / W), bc = b % W;
      for (const [dr, dc, ch] of DIRS) {
        const pr = br - dr, pc = bc - dc;
        const tr = br + dr, tc = bc + dc;
        if (pr < 0 || pc < 0 || pc >= W || tr < 0 || tc < 0 || tc >= W) continue;
        const pushCell = pr * W + pc;
        const target = tr * W + tc;
        if (!region.has(pushCell)) continue;
        if (!cells.has(target) || boxSet.has(target) || !live.has(target)) continue;
        const nb = [...node.boxes];
        nb[bi] = target;
        nb.sort((a, b2) => a - b2);
        const nRegion = reach(b, new Set(nb), cells, W, H);
        const k = keyOf(nb, lowest(nRegion));
        if (seen.has(k)) continue;
        const walk = walkPath(node.player, pushCell, boxSet, cells, W, H);
        if (walk === null) continue;
        seen.add(k);
        const idx = nodes.length;
        nodes.push({ boxes: nb, player: b, parent: ni, step: walk + ch });
        if (solved(nb)) {
          let text = '';
          let n = idx;
          while (n !== 0) {
            text = nodes[n].step + text;
            n = nodes[n].parent;
          }
          return { text, player: b, boxes: nb };
        }
        q.push(idx);
      }
    }
  }
  return null;
}

// Split the level into rooms: cut the hallway row (the player's row),
// flood-fill the remaining floor. Each component holding boxes is a room;
// its door is the lowest hallway square next to it. Returns null when
// the shape is not the generator's (caller falls back to whole-level).
function roomsOf(p) {
  const { W, H, wall, goals, boxes, player } = p;
  const hallRow = Math.floor(player / W);
  const cells = new Set();
  for (let i = 0; i < p.N; i++) {
    if (!wall[i] && Math.floor(i / W) !== hallRow) cells.add(i);
  }
  const seen = new Set();
  const rooms = [];
  for (const s of cells) {
    if (seen.has(s)) continue;
    const comp = new Set([s]);
    const q = [s];
    seen.add(s);
    for (let h = 0; h < q.length; h++) {
      const cur = q[h];
      const r = Math.floor(cur / W), c = cur % W;
      for (const [dr, dc] of DIRS) {
        const nr = r + dr, nc = c + dc;
        if (nr < 0 || nc < 0 || nc >= W || nr >= H) continue;
        const ni = nr * W + nc;
        if (!cells.has(ni) || seen.has(ni)) continue;
        seen.add(ni);
        comp.add(ni);
        q.push(ni);
      }
    }
    const rb = boxes.filter(b => comp.has(b));
    if (rb.length === 0) continue;
    const rg = new Set([...goals].filter(g => comp.has(g)));
    if (rb.length !== rg.size) return null;
    let door = -1;
    for (const cell of comp) {
      const r = Math.floor(cell / W), c = cell % W;
      for (const [dr, dc] of DIRS) {
        const nr = r + dr, nc = c + dc;
        if (nr !== hallRow || nc < 0 || nc >= W) continue;
        const ni = nr * W + nc;
        if (!wall[ni] && (door === -1 || ni < door)) door = ni;
      }
    }
    if (door === -1) return null;
    const rc = new Set(comp);
    rc.add(door);
    rooms.push({ cells: rc, boxes: rb, goals: rg, door, low: Math.min(...comp) });
  }
  rooms.sort((a, b) => a.low - b.low);
  return rooms;
}

function solveLevel(level) {
  const p = parse(level);
  const live = liveSquares(p.wall, p.goals, p.W, p.H);
  const allFloor = new Set();
  for (let i = 0; i < p.N; i++) if (!p.wall[i]) allFloor.add(i);
  const rooms = roomsOf(p);
  if (!rooms) {
    const r = solveRoom(allFloor, p.boxes, p.goals, p.player, live, p.W, p.H);
    return r ? r.text : '';
  }
  let moves = '';
  let curPlayer = p.player;
  let curBoxes = [...p.boxes];
  for (const room of rooms) {
    const boxSet = new Set(curBoxes);
    const walk = walkPath(curPlayer, room.door, boxSet, allFloor, p.W, p.H);
    if (walk === null) return '';
    moves += walk;
    const res = solveRoom(room.cells, room.boxes, room.goals, room.door, live, p.W, p.H);
    if (!res) return '';
    moves += res.text;
    curPlayer = res.player;
    const roomBoxSet = new Set(room.boxes);
    curBoxes = curBoxes.filter(b => !roomBoxSet.has(b)).concat(res.boxes);
  }
  return moves;
}

for (const id of readdirSync(IN).sort()) {
  let moves = '';
  try {
    moves = solveLevel(readFileSync(join(IN, id, 'level.txt'), 'utf8'));
  } catch {
    moves = '';
  }
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'solution.txt'), `${moves}\n`);
}

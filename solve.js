// A line diff that returns exactly what makefun-diff 1.0.0 returns, faster.
//
// The rule, from the house program: lines are cut after every "\n" (a "\r" is
// part of its line); a last line with no "\n" is a line too. The lines both
// texts share at the start are kept, then the lines both share at the end of
// what is left. Between them Myers's greedy search runs: for d edits and each
// diagonal k = x - y, the furthest point a path of d edits reaches on k is
// one old line past the furthest (d-1)-point on k - 1 (a deletion) or one new
// line past the furthest (d-1)-point on k + 1 (an insertion), whichever lies
// further into the old text, the deletion when both reach the same point; a
// move past the end of either text is no candidate. From that point the path
// keeps every line equal in both texts as far as it can. The first path to
// reach the ends of both texts is the edit script.
//
// Speed, against the house program's linked list of path objects and its
// string compares: lines are hashed to integers once, so every comparison in
// the search is an integer compare; the search keeps one Int32Array of
// furthest x per d (indexed by diagonal), no object per step; the script is
// rebuilt by walking those arrays back from the end.

/** The kept lines a hunk shows before and after each change run. */
const CONTEXT = 3;

/** A text's lines, each with its "\n" (the last one without, when the text does not end in one). */
function tokenize(text) {
  const parts = text.split('\n');
  const lines = new Array(parts.length);
  const last = parts.length - 1;
  for (let i = 0; i < last; i++) lines[i] = `${parts[i]}\n`;
  if (parts[last] !== '') {
    lines[last] = parts[last];
    return lines;
  }
  lines.length = last;
  return lines;
}

/**
 * The runs of the edit script of the middle slices a into b, as integer line
 * ids: [{ kind, count }], in order, kind 0 kept, 1 deleted, 2 inserted.
 * The search's furthest-x arrays, one per d, are kept so the script can be
 * walked back from the end; an entry of -2 means that diagonal held no path.
 */
function editRuns(a, b) {
  const n = a.length;
  const m = b.length;
  const vs = [];
  // d = 0: the initial snake from before either text's first line.
  let x = -1;
  while (x + 1 < n && x + 1 < m && a[x + 1] === b[x + 1]) x++;
  const v0 = new Int32Array(1);
  v0[0] = x;
  vs.push(v0);
  let dFinal = 0;
  let kFinal = 0;
  if (x + 1 < n || x + 1 < m) {
    let done = false;
    for (let d = 1; !done; d++) {
      const v = new Int32Array(d + 1);
      v.fill(-2);
      const prev = vs[d - 1];
      // j indexes the diagonal: k = 2j - d, so j runs 0..d and the two
      // predecessors are prev[j - 1] (a deletion, from k - 1) and prev[j]
      // (an insertion, from k + 1).
      for (let j = 0; j <= d; j++) {
        const k = (j << 1) - d;
        const removeX = j > 0 ? prev[j - 1] : -2;
        const addX = j < d ? prev[j] : -2;
        const canRemove = removeX !== -2 && removeX + 1 < n;
        const canAdd = addX !== -2 && addX - k < m;
        if (!canRemove && !canAdd) continue;
        const byDeletion = canRemove ? removeX + 1 : -2;
        const byInsertion = canAdd ? addX : -2;
        let px = byDeletion >= byInsertion ? byDeletion : byInsertion;
        let py = px - k;
        while (px + 1 < n && py + 1 < m && a[px + 1] === b[py + 1]) {
          px++;
          py++;
        }
        v[j] = px;
        if (px + 1 >= n && py + 1 >= m) {
          dFinal = d;
          kFinal = k;
          done = true;
          break;
        }
      }
      vs.push(v);
    }
  }
  // Walk the search back from its end, collecting the script in reverse:
  // at each d, the snake that led into this point, then the one edit.
  const reversed = [];
  let k = kFinal;
  for (let d = dFinal; d >= 1; d--) {
    const v = vs[d];
    const prev = vs[d - 1];
    const j = (k + d) >> 1;
    const px = v[j];
    const removeX = j - 1 >= 0 ? prev[j - 1] : -2;
    const addX = j <= d - 1 ? prev[j] : -2;
    const canRemove = removeX !== -2 && removeX + 1 < n;
    const canAdd = addX !== -2 && addX - k < m;
    const byDeletion = canRemove ? removeX + 1 : -2;
    const byInsertion = canAdd ? addX : -2;
    const isDeletion = byDeletion >= byInsertion;
    const afterMove = isDeletion ? byDeletion : byInsertion;
    const snake = px - afterMove;
    if (snake > 0) reversed.push({ kind: 0, count: snake });
    reversed.push({ kind: isDeletion ? 1 : 2, count: 1 });
    k = isDeletion ? k - 1 : k + 1;
  }
  const firstSnake = vs[0][0] + 1;
  if (firstSnake > 0) reversed.push({ kind: 0, count: firstSnake });
  // Reverse, merging runs of one kind the way the house program's path does.
  const runs = [];
  for (let i = reversed.length - 1; i >= 0; i--) {
    const r = reversed[i];
    const last = runs.length > 0 ? runs[runs.length - 1] : undefined;
    if (last !== undefined && last.kind === r.kind) last.count += r.count;
    else runs.push({ kind: r.kind, count: r.count });
  }
  return runs;
}

/** A line as the patch writes it: its op, the line, a newline, and "%" on a line of its own when it had none. */
function written(op, line) {
  return line.endsWith('\n') ? `${op}${line}` : `${op}${line}\n%\n`;
}

/** makefun-diff 1.0.0's answer for one case's input. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const a = tokenize(input.old);
  const b = tokenize(input.new);
  const n = a.length;
  const m = b.length;
  // Hash every line to an integer id once, so the search compares integers.
  const ids = new Map();
  const hash = (lines) => {
    const out = new Int32Array(lines.length);
    for (let i = 0; i < lines.length; i++) {
      let id = ids.get(lines[i]);
      if (id === undefined) {
        id = ids.size;
        ids.set(lines[i], id);
      }
      out[i] = id;
    }
    return out;
  };
  const ai = hash(a);
  const bi = hash(b);
  // The common prefix, then the common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && ai[prefix] === bi[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && ai[n - 1 - suffix] === bi[m - 1 - suffix]) suffix++;
  const runs = [];
  if (prefix > 0) runs.push({ kind: 0, count: prefix });
  runs.push(...editRuns(ai.subarray(prefix, n - suffix), bi.subarray(prefix, m - suffix)));
  if (suffix > 0) runs.push({ kind: 0, count: suffix });

  // The change runs: each a stretch of deletions and insertions between two kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === 0) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes.length > 0 ? changes[changes.length - 1] : undefined;
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === 1) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks.length > 0 ? hunks[hunks.length - 1] : undefined;
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }
  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written('=', a[at]));
      for (let i = 0; i < c.dels; i++) out.push(written('-', a[c.o + i]));
      for (let i = 0; i < c.ins; i++) out.push(written('+', b[c.p + i]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written('=', a[at]));
  }
  return out.join('');
}

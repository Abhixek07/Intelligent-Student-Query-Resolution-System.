# Intelligent-Student-Query-Resolution-System.
DSA
"""Intelligent Student Query Resolution System (ISQRS) - DSA-II PBL.
BST + AVL query store, heap priority queue, graph of related queries."""
import heapq, itertools, re
from collections import deque, Counter
 
def normalize(q):                       # duplicate-handling step
    return re.sub(r"[^a-z0-9 ]", "", q.lower()).strip()
 
class Node:
    def __init__(s, key, cat, ans): s.key, s.cat, s.ans = key, cat, ans; s.l = s.r = None; s.h = 1
 
class BST:                              # Module 3: query/FAQ store
    def __init__(s): s.root, s.size = None, 0
    def insert(s, q, cat, ans):
        k, p, n = normalize(q), None, s.root
        while n:
            if k == n.key: return False            # duplicate rejected
            p, n = n, (n.l if k < n.key else n.r)
        nn = Node(k, cat, ans); s.size += 1
        if not p: s.root = nn
        elif k < p.key: p.l = nn
        else: p.r = nn
        return True
    def search(s, q):
        k, n = normalize(q), s.root
        while n and n.key != k: n = n.l if k < n.key else n.r
        return n
    def delete(s, q): s.root, ok = s._del(s.root, normalize(q)); s.size -= ok; return bool(ok)
    def _del(s, n, k):
        if not n: return None, 0
        if k < n.key: n.l, ok = s._del(n.l, k)
        elif k > n.key: n.r, ok = s._del(n.r, k)
        else:
            if not n.l: return n.r, 1
            if not n.r: return n.l, 1
            m = n.r
            while m.l: m = m.l
            n.key, n.cat, n.ans = m.key, m.cat, m.ans
            n.r, _ = s._del(n.r, m.key); ok = 1
        return n, ok
    def inorder(s):
        out, st, n = [], [], s.root
        while st or n:
            while n: st.append(n); n = n.l
            n = st.pop(); out.append(n.key); n = n.r
        return out
    def order(s, kind="in", n="r"):     # pre / in / post-order traversal
        n = s.root if n == "r" else n
        if not n: return []
        L, R = s.order(kind, n.l), s.order(kind, n.r)
        return {"pre": [n.key] + L + R, "in": L + [n.key] + R, "post": L + R + [n.key]}[kind]
    def height(s):                      # iterative level count (safe for skewed trees)
        lvl, h = ([s.root] if s.root else []), 0
        while lvl: h += 1; lvl = [c for n in lvl for c in (n.l, n.r) if c]
        return h
 
class AVL(BST):                         # Module 5: balanced store
    h = staticmethod(lambda n: n.h if n else 0)
    def _fix(s, n): n.h = 1 + max(s.h(n.l), s.h(n.r))
    def _rr(s, y): x = y.l; y.l, x.r = x.r, y; s._fix(y); s._fix(x); return x
    def _rl(s, x): y = x.r; x.r, y.l = y.l, x; s._fix(x); s._fix(y); return y
    def insert(s, q, cat, ans):
        k = normalize(q)
        if s.search(k): return False
        s.root = s._ins(s.root, k, cat, ans); s.size += 1; return True
    def _ins(s, n, k, cat, ans):
        if not n: return Node(k, cat, ans)
        if k < n.key: n.l = s._ins(n.l, k, cat, ans)
        else: n.r = s._ins(n.r, k, cat, ans)
        s._fix(n); b = s.h(n.l) - s.h(n.r)
        if b > 1:
            if k > n.l.key: n.l = s._rl(n.l)
            return s._rr(n)
        if b < -1:
            if k < n.r.key: n.r = s._rr(n.r)
            return s._rl(n)
        return n
 
class PriorityQueue:                    # Module 4: urgency ranking (binary min-heap)
    W = 0.5                             # waiting-time weight
    def __init__(s): s.h, s.c, s.t = [], itertools.count(), 0
    def push(s, q, urgency):            # score = urgency + W * waiting ticks (stored via arrival)
        heapq.heappush(s.h, (-(urgency) + s.W * s.t, next(s.c), q, urgency)); s.t += 1
    def pop(s): return heapq.heappop(s.h)[2] if s.h else None
    def peek(s): return s.h[0][2] if s.h else None
 
class Graph:                            # Module 5: related queries/topics (weighted, adjacency list)
    def __init__(s): s.adj = {}
    def link(s, a, b, w=1): s.adj.setdefault(a, {})[b] = w; s.adj.setdefault(b, {})[a] = w
    def related(s, start, depth=2):     # BFS up to given depth
        seen, dq, out = {start}, deque([(start, 0)]), []
        while dq:
            u, d = dq.popleft()
            if d == depth: continue
            for v in sorted(s.adj.get(u, ())):
                if v not in seen: seen.add(v); out.append(v); dq.append((v, d + 1))
        return out
    def components(s):                  # DFS connected components
        seen, out = set(), []
        for v in sorted(s.adj):
            if v in seen: continue
            comp, st = [], [v]; seen.add(v)
            while st:
                u = st.pop(); comp.append(u)
                for x in s.adj[u]:
                    if x not in seen: seen.add(x); st.append(x)
            out.append(sorted(comp))
        return out
    def dijkstra(s, src):               # closest topics (smaller weight = more related)
        dist, pq = {src: 0}, [(0, src)]
        while pq:
            d, u = heapq.heappop(pq)
            if d > dist[u]: continue
            for v, w in s.adj[u].items():
                if d + w < dist.get(v, 1e9): dist[v] = d + w; heapq.heappush(pq, (d + w, v))
        return dist
    def kruskal(s):                     # minimum spanning tree (topic backbone)
        p = {v: v for v in s.adj}
        def f(x):
            while p[x] != x: p[x] = p[p[x]]; x = p[x]
            return x
        out = []
        for w, a, b in sorted((w, a, b) for a in s.adj for b, w in s.adj[a].items() if a < b):
            ra, rb = f(a), f(b)
            if ra != rb: p[ra] = rb; out.append((a, b, w))
        return out
 
def lcs(a, b):                          # Unit 3 DP: longest common subsequence
    t = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(len(a)):
        for j in range(len(b)):
            t[i+1][j+1] = t[i][j] + 1 if a[i] == b[j] else max(t[i][j+1], t[i+1][j])
    return t[-1][-1]
 
def knapsack(items, cap):               # Unit 3 DP: 0/1 knapsack; items = (name, minutes, urgency)
    n = len(items); t = [[0] * (cap + 1) for _ in range(n + 1)]
    for i, (_, w, v) in enumerate(items, 1):
        for c in range(cap + 1):
            t[i][c] = max(t[i-1][c], t[i-1][c-w] + v) if c >= w else t[i-1][c]
    c, pick = cap, []
    for i in range(n, 0, -1):
        if t[i][c] != t[i-1][c]: pick.append(items[i-1][0]); c -= items[i-1][1]
    return t[n][cap], pick[::-1]
 
def heap_sort(a):                       # Unit 1: in-place max-heap sort (ascending)
    a, n = list(a), len(a)
    def sift(i, n):
        while 2 * i + 1 < n:
            j = 2 * i + 1
            if j + 1 < n and a[j+1] > a[j]: j += 1
            if a[i] >= a[j]: break
            a[i], a[j] = a[j], a[i]; i = j
    for i in range(n // 2 - 1, -1, -1): sift(i, n)
    for e in range(n - 1, 0, -1): a[0], a[e] = a[e], a[0]; sift(0, e)
    return a
 
def huffman(text):                      # Unit 1 application: Huffman codes for stored answers
    h = [[w, i, {ch: ""}] for i, (ch, w) in enumerate(Counter(text).items())]
    heapq.heapify(h); k = len(h)
    while len(h) > 1:
        a, b = heapq.heappop(h), heapq.heappop(h)
        m = {c: "0" + v for c, v in a[2].items()} | {c: "1" + v for c, v in b[2].items()}
        heapq.heappush(h, [a[0] + b[0], k, m]); k += 1
    return h[0][2]
 
class ISQRS:                            # integration
    def __init__(s): s.store, s.pq, s.g = AVL(), PriorityQueue(), Graph()
    def add_faq(s, q, cat, ans): return s.store.insert(q, cat, ans)
    def similar(s, q, th=0.8):          # nearest stored query by LCS ratio
        k = normalize(q); best = max(s.store.inorder(), key=lambda x: lcs(k, x), default=None)
        return best if best and lcs(k, best) / max(len(k), len(best)) >= th else None
    def ask(s, q, urgency=1):
        n = s.store.search(q)
        if n: return n.ans, s.g.related(n.cat)
        s.pq.push(q, urgency); return None, []      # unanswered -> urgent queue


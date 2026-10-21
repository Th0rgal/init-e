#!/usr/bin/env python3
"""Executable model of the bounded Patricia table experiment.

Semantics mirror htab.pnk: insertion-order iteration, in-place update,
swap-remove deletion, tail truncation, packed-key order.
"""
from __future__ import annotations
import random
from collections import OrderedDict


def bit_at(key: bytes, pos: int) -> int:
    return (key[pos >> 3] >> (7 - (pos & 7))) & 1


def first_diff(a: bytes, b: bytes) -> int:
    for i, (x, y) in enumerate(zip(a, b)):
        z = x ^ y
        if z:
            return i * 8 + (7 - (z.bit_length() - 1))
    raise ValueError("equal keys")


class Patricia:
    """Capacity-bounded Patricia model with the PNK free/order accounting.

    Node ids are opaque here; `live_internal` is checked against the PNK pool
    bound cap/2, and `_grow` performs the same order-preserving rebuild.
    """
    def __init__(self, key_len: int, cap: int = 8):
        self.key_len = key_len
        self.cap = cap
        self.root = None
        self.nodes = {}          # id -> ('leaf', key, value) | ('int', bit, left, right)
        self.next_id = 1
        self.order = []          # ordinal -> leaf id
        self.order_pos = {}      # leaf id -> ordinal
        self.max_visits = 0
        self.live_internal = 0
        self.max_live_internal = 0
        # deterministic operation counters
        self.visits = 0
        self.bit_tests = 0
        self.key_compares = 0
        self.compare_bytes = 0
        self.first_diff_bytes = 0
        self.order_moves = 0
        self.grows = 0
        self.copy_moves = 0
        self.path_stores = 0
        self.bsearch_steps = 0
        self.link_writes = 0

    def _new(self, node) -> int:
        i = self.next_id
        self.next_id += 1
        self.nodes[i] = node
        return i

    def _walk(self, key: bytes):
        """Return (leaf_id_or_None, path) while counting a real lookup."""
        if self.root is None:
            return None, []
        node = self.root
        path = []
        visits = 0
        while self.nodes[node][0] == 'int':
            visits += 1
            self.visits += 1
            self.bit_tests += 1
            _, bit, left, right = self.nodes[node]
            side = bit_at(key, bit)
            path.append((node, side))
            node = left if side == 0 else right
        self.max_visits = max(self.max_visits, visits)
        self.key_compares += 1
        self.compare_bytes += self.key_len
        return node, path

    def _leaf_id(self, key: bytes):
        lid, _ = self._walk(key)
        if lid is None:
            return None
        return lid if self.nodes[lid][1] == key else None

    def get(self, key: bytes, default=None):
        lid = self._leaf_id(key)
        return default if lid is None else self.nodes[lid][2]

    def _grow(self) -> None:
        old_items = self.items()
        old = self
        new = Patricia(self.key_len, self.cap * 2)
        for k, v in old_items:
            new.set(k, v)
        # Count the rebuild work in the old table's totals.
        for name in ('visits', 'bit_tests', 'key_compares', 'compare_bytes',
                     'first_diff_bytes', 'order_moves', 'path_stores',
                     'bsearch_steps', 'link_writes'):
            setattr(old, name, getattr(old, name) + getattr(new, name))
        old.max_visits = max(old.max_visits, new.max_visits)
        old.grows += 1
        old.copy_moves += len(old_items)
        old.cap = new.cap
        old.root = new.root
        old.nodes = new.nodes
        old.next_id = new.next_id
        old.order = new.order
        old.order_pos = new.order_pos
        old.live_internal = new.live_internal
        old.max_live_internal = max(old.max_live_internal, new.max_live_internal)

    def set(self, key: bytes, value) -> bool:
        assert len(key) == self.key_len
        if self.root is None:
            lid = self._new(('leaf', key, value))
            self.root = lid
            self.order.append(lid)
            self.order_pos[lid] = 0
            return True
        node, path = self._walk(key)
        old = self.nodes[node][1]
        if old == key:
            self.nodes[node] = ('leaf', key, value)
            return False
        if (len(self.order) + 1) * 2 > self.cap:
            self._grow()
            node, _ = self._walk(key)
            old = self.nodes[node][1]
            if old == key:
                self.nodes[node] = ('leaf', key, value)
                return False
        d = first_diff(key, old)
        self.first_diff_bytes += self.key_len
        new_leaf = self._new(('leaf', key, value))
        new_int = self._new(('int', d, None, None))
        self.path_stores += len(path)
        self.bsearch_steps += max(1, len(path).bit_length())
        self.link_writes += 1
        self.live_internal += 1
        self.max_live_internal = max(self.max_live_internal, self.live_internal)
        parent = None
        direction = None
        cur = self.root
        while self.nodes[cur][0] == 'int' and self.nodes[cur][1] < d:
            self.visits += 1
            self.bit_tests += 1
            parent = cur
            _, bit, left, right = self.nodes[cur]
            direction = bit_at(key, bit)
            cur = left if direction == 0 else right
        if bit_at(key, d) == 0:
            self.nodes[new_int] = ('int', d, new_leaf, cur)
        else:
            self.nodes[new_int] = ('int', d, cur, new_leaf)
        if parent is None:
            self.root = new_int
        else:
            _, bit, l, r = self.nodes[parent]
            self.nodes[parent] = ('int', bit, new_int if direction == 0 else l,
                                  new_int if direction == 1 else r)
        self.order.append(new_leaf)
        self.order_pos[new_leaf] = len(self.order) - 1
        return True

    def delete(self, key: bytes) -> bool:
        lid, _ = self._walk(key)
        if lid is None or self.nodes[lid][1] != key:
            return False
        if self.root == lid:
            self.root = None
        else:
            stack = []
            cur = self.root
            while self.nodes[cur][0] == 'int':
                self.visits += 1
                self.bit_tests += 1
                _, bit, left, right = self.nodes[cur]
                side = bit_at(key, bit)
                stack.append((cur, side))
                cur = left if side == 0 else right
            parent, direction = stack[-1]
            _, pbit, left, right = self.nodes[parent]
            sibling = right if direction == 0 else left
            if len(stack) == 1:
                self.root = sibling
            else:
                gp, gdir = stack[-2]
                _, gbit, gl, gr = self.nodes[gp]
                self.nodes[gp] = ('int', gbit, sibling if gdir == 0 else gl,
                                  sibling if gdir == 1 else gr)
            del self.nodes[parent]
            self.live_internal -= 1
        del self.nodes[lid]
        pos = self.order_pos.pop(lid)
        last = len(self.order) - 1
        if pos != last:
            self.order_moves += 1
            moved = self.order[last]
            self.order[pos] = moved
            self.order_pos[moved] = pos
        self.order.pop()
        return True

    def truncate(self, n: int) -> None:
        while len(self.order) > n:
            lid = self.order[-1]
            self.delete(self.nodes[lid][1])

    def items(self):
        return [(self.nodes[lid][1], self.nodes[lid][2]) for lid in self.order]

    def stats(self):
        return {
            'cap': self.cap, 'count': len(self.order), 'grows': self.grows,
            'copy_moves': self.copy_moves, 'max_visits': self.max_visits,
            'path_stores': self.path_stores, 'bsearch_steps': self.bsearch_steps,
            'link_writes': self.link_writes,
            'max_live_internal': self.max_live_internal,
            'visits': self.visits, 'bit_tests': self.bit_tests,
            'key_compares': self.key_compares,
            'compare_bytes': self.compare_bytes,
            'first_diff_bytes': self.first_diff_bytes,
            'order_moves': self.order_moves,
        }


class Reference:
    def __init__(self, key_len: int):
        self.d = OrderedDict()

    def get(self, key, default=None):
        return self.d.get(key, default)

    def set(self, key, value):
        new = key not in self.d
        self.d[key] = value
        return new

    def delete(self, key):
        if key not in self.d:
            return False
        # swap-remove order semantics
        keys = list(self.d.keys())
        pos = keys.index(key)
        last = keys[-1]
        if pos != len(keys) - 1:
            val = self.d.pop(last)
            self.d.pop(key)
            # rebuild preserving positions with moved last at pos
            items = list(self.d.items())
            items.insert(pos, (last, val))
            self.d = OrderedDict(items)
        else:
            self.d.pop(key)
        return True

    def truncate(self, n):
        while len(self.d) > n:
            self.d.popitem(last=True)

    def items(self):
        return list(self.d.items())


def randkey(rng, L):
    return bytes(rng.randrange(256) for _ in range(L))


def check(L=32, steps=20000, seed=1):
    rng = random.Random(seed)
    p = Patricia(L)
    r = Reference(L)
    live = []
    for step in range(steps):
        op = rng.random()
        if op < 0.60 or not live:
            k = randkey(rng, L)
            v = rng.randrange(1 << 30)
            assert p.set(k, v) == r.set(k, v)
            if k not in live:
                live.append(k)
        elif op < 0.88:
            k = rng.choice(live)
            assert p.delete(k) == r.delete(k)
            live.remove(k)
        else:
            n = rng.randrange(0, len(live) + 1)
            p.truncate(n)
            r.truncate(n)
            live = live[:n]
        assert p.items() == r.items(), (step, p.items()[:5], r.items()[:5])
        assert p.live_internal <= p.cap // 2, (p.live_internal, p.cap)
    for k, v in r.items():
        assert p.get(k) == v
    assert p.items() == r.items()
    return p.stats()


def adversarial(L=20):
    n = 5000
    p = Patricia(L)
    for i in range(n):
        # big-endian n in both 8-byte halves, zero tail
        k = i.to_bytes(8, 'big') + i.to_bytes(8, 'big') + b'\0' * (L - 16)
        p.set(k, 1)
    # repeated lookups must be bounded by depth, not cluster size
    worst = 0
    for _ in range(2000):
        for i in range(0, n, 137):
            k = i.to_bytes(8, 'big') + i.to_bytes(8, 'big') + b'\0' * (L - 16)
            assert p.get(k) == 1
            worst = max(worst, p.max_visits)
    assert p.live_internal <= p.cap // 2
    return p.stats(), worst


if __name__ == '__main__':
    import json
    for L in (20, 28, 32, 52, 60):
        st = check(L=L, steps=5000, seed=L)
        print('random L=%d' % L, json.dumps(st, sort_keys=True))
    for L in (20, 32, 60):
        st, worst = adversarial(L)
        st['repeat_max_visits'] = worst
        print('adversarial L=%d' % L, json.dumps(st, sort_keys=True))

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
    def __init__(self, key_len: int):
        self.key_len = key_len
        self.root = None
        self.nodes = {}          # id -> ('leaf', key, value) | ('int', bit, left, right)
        self.next_id = 1
        self.order = []          # ordinal -> leaf id
        self.order_pos = {}      # leaf id -> ordinal
        self.max_visits = 0

    def _new(self, node) -> int:
        i = self.next_id
        self.next_id += 1
        self.nodes[i] = node
        return i

    def _leaf_id(self, key: bytes):
        if self.root is None:
            return None
        node = self.root
        visits = 0
        while self.nodes[node][0] == 'int':
            visits += 1
            _, bit, left, right = self.nodes[node]
            node = left if bit_at(key, bit) == 0 else right
        self.max_visits = max(self.max_visits, visits)
        lid = node
        if self.nodes[lid][1] == key:
            return lid
        return None

    def get(self, key: bytes, default=None):
        lid = self._leaf_id(key)
        return default if lid is None else self.nodes[lid][2]

    def set(self, key: bytes, value) -> bool:
        assert len(key) == self.key_len
        if self.root is None:
            lid = self._new(('leaf', key, value))
            self.root = lid
            self.order.append(lid)
            self.order_pos[lid] = 0
            return True
        node = self.root
        while self.nodes[node][0] == 'int':
            _, bit, left, right = self.nodes[node]
            node = left if bit_at(key, bit) == 0 else right
        lid = node
        old = self.nodes[lid][1]
        if old == key:
            self.nodes[lid] = ('leaf', key, value)
            return False
        d = first_diff(key, old)
        new_leaf = self._new(('leaf', key, value))
        new_int = self._new(('int', d, None, None))
        # Walk down to the insertion point, remembering parent/direction.
        parent = None
        direction = None
        cur = self.root
        while self.nodes[cur][0] == 'int' and self.nodes[cur][1] < d:
            parent = cur
            _, bit, left, right = self.nodes[cur]
            direction = 0 if bit_at(key, bit) == 0 else 1
            cur = left if direction == 0 else right
        _, _, left, right = self.nodes[new_int]
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
        lid = self._leaf_id(key)
        if lid is None:
            return False
        if self.root == lid:
            self.root = None
        else:
            stack = []
            cur = self.root
            while self.nodes[cur][0] == 'int':
                _, bit, left, right = self.nodes[cur]
                if bit_at(key, bit) == 0:
                    stack.append((cur, 0))
                    cur = left
                else:
                    stack.append((cur, 1))
                    cur = right
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
        del self.nodes[lid]
        pos = self.order_pos.pop(lid)
        last = len(self.order) - 1
        if pos != last:
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
    for k, v in r.items():
        assert p.get(k) == v
    return p.max_visits


def adversarial():
    L = 20
    n = 5000
    p = Patricia(L)
    for i in range(n):
        # big-endian n in both 8-byte halves, zero 4-byte tail
        k = i.to_bytes(8, 'big') + i.to_bytes(8, 'big') + b'\0' * 4
        p.set(k, 1)
    # repeated lookups must be bounded by depth, not cluster size
    worst = 0
    for _ in range(2000):
        for i in range(0, n, 137):
            k = i.to_bytes(8, 'big') + i.to_bytes(8, 'big') + b'\0' * 4
            assert p.get(k) == 1
            worst = max(worst, p.max_visits)
    return len(p.order), worst


if __name__ == '__main__':
    print('random max visits:', check())
    print('adversarial leaves/max visits:', adversarial())

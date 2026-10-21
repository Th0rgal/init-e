# Bounded deterministic table replacement (participant-only experiment)

Branch: `feat/bounded-table-experiment` (from green `feat/cost-guest-bound` @ 071d7f23c).
No files under `Guest/`, `guest/`, or `InitE/` are modified.

## 1. Current htab contract (audited)

`guest/src/lib/htab.pnk` is an open-addressing table with linear probing and
backward-shift deletion. Header fields are observable by clients only through
`HT_KEYLEN` and `HT_COUNT`; every other access goes through the API.

Direct field clients (all other accesses are API calls):

| file:line | field | purpose |
|---|---|---|
| `guest/src/fork.pnk:705` | `HT_COUNT` | number of deferred deletes |
| `guest/src/state.pnk:140,161` | `HT_KEYLEN` | copy/merge stride and key length |
| `guest/src/state.pnk:446,452` | `HT_COUNT` | non-empty checks |
| `guest/src/state.pnk:546,669,691` | `HT_COUNT` | union / nested-map iteration bound |
| `guest/src/block.pnk:285,303,356` | `HT_COUNT` | iteration bound / empty checks |
| `guest/src/bal.pnk:300,341,347,644,654,677,718,726,727` | `HT_COUNT` | iteration / recursive size accounting |
| `guest/src/bal.pnk:674,675` | `HT_COUNT` | witness size accounting |

API surface and semantics that must be preserved:

- `htab_new(key_len, cap)`, `htab_new_scratch(key_len, cap)`: fresh table.
- `htab_get`, `htab_has`: lookup.
- `htab_set`: update existing value in place (does not change insertion ordinal),
  or append a new key at the next ordinal.
- `htab_del`: remove by key; memoryless `swap-remove` of the order entry:
  the last order entry is moved into the deleted ordinal.
- `htab_truncate(t, n)`: delete the last `count - n` order entries.
- `htab_item(t, ordinal) -> <used, key_ptr, value>`: **insertion order**.
- `htab_slot(t, i) -> <used, key_ptr, value>`: slot-shaped access used only by
  `htab_item`; no external client.
- `htab_keys(t) -> <packed_keys, count>`: keys copied at
  `stride = (key_len + 7) & -8`, including padding.
- `htab_count`, `htab_cap`.
- `htab_copy`, `htab_copy_scratch`: independent deep/shallow copies; scratch
  version uses the frame allocator.
- `htab_grow`, `htab_insert_raw`, `htab_find_slot`: internal helpers, no
  external callers.
- `htab_union_into` (in `state.pnk`, not `lib/htab.pnk`): iterates
  `i < HT_COUNT` and calls `htab_item(src, i)`, then `htab_set(dst, key, value)`.

Key lengths actually allocated: 20, 28, 32, 52, 60 bytes. Maximum bit index
is therefore 480. Initial caps are powers of two up to 256; growth doubles.

## 2. Replacement: compressed binary Patricia trie + order arrays

The table keeps the existing 72-byte header prefix, so `HT_KEYLEN` and
`HT_COUNT` clients are unchanged, and appends internal fields:

```
0  HT_KEYLEN     8  HT_KEYSTRIDE  16 HT_CAP      24 HT_COUNT
32 HT_KEYS      40 HT_VALS       48 HT_USED     56 HT_ORDER
64 HT_ORDER_POS 72 HT_ROOT       80 HT_LEAF_FREE 88 HT_INT_FREE
96 HT_SIZE
```

`HT_CAP` remains the entry capacity used by `htab_cap`; it doubles exactly as
before. `HT_COUNT` remains the number of live keys.

Storage (all capacities are in entries, `n = HT_CAP`):

- leaf ids `1..n`: key bytes at `HT_KEYS + (id-1)*stride`, value at
  `HT_VALS + (id-1)*8`, order-position at `HT_ORDER_POS + (id-1)*8`.
- internal ids `n+1 .. n+n/2`: 24-byte nodes
  `[child0, child1, bit]`; node index `id-(n+1)`.
- `HT_ORDER[ordinal] = leaf_id`; `HT_LEAF_FREE` is a singly linked free list
  threaded through `HT_VALS`; `HT_INT_FREE` through internal `child0`.
- root id in `HT_ROOT` (0 = empty).

The load-factor invariant `count <= n/2` is preserved from `htab_set`. Since a
Patricia tree with `N` leaves has exactly `N-1` internal nodes and
`N-1 <= n/2-1`, the `n/2` internal-node pool is sufficient. No per-entry
`used` array is needed; a leaf is live iff it is reachable and in the order
array.

### Lookup

1. If root is 0, absent.
2. While internal: read `bit`, test key bit `bit` (MSB-first within each byte),
   descend left/right.
3. At the leaf, one `memeq(key, leaf_key, key_len)`.

Work: at most `8*key_len` internal descents plus one `key_len`-byte compare.
No capacity-dependent scan, no hash quality assumption.

### Insert

1. Lookup path to leaf/subtree.
2. If leaf key equals, store value (order unchanged).
3. If absent, scan the new key and the reached leaf key for the first differing
   bit `d` (`O(key_len)`).
4. Walk down while internal `node.bit < d`, recording the parent.
5. Allocate one leaf and one internal node at bit `d`; new internal has the new
   leaf and the old subtree as children; link it to the parent or root.
6. Append leaf id to `HT_ORDER[count]`, set `HT_ORDER_POS[leaf] = count`,
   increment count. If `2*(count+1) > n`, grow first.

Work: `O(key_len)` bit tests + `O(key_len)` first-difference scan + `O(1)`
node links + one order append. Growth is amortized `O(key_len)` per insertion
because capacity doubles and all entries are reinserted from `HT_ORDER`.

### Delete

1. Find leaf and its parent internal + sibling (bit tests + `memeq`).
2. Replace parent by sibling in grandparent/root; free leaf and parent.
3. `pos = HT_ORDER_POS[leaf]`, `last = count-1`; if `pos != last`, move
   `HT_ORDER[last]` to `pos` and update its `HT_ORDER_POS` (exact current
   swap-remove semantics); decrement count.

Work: `O(key_len)` search + `O(1)` unlink/order fix. No backward-shift scan.

### Truncate / iteration / union / copy

- `htab_truncate(t,n)`: while `count > n`, take `leaf = HT_ORDER[count-1]`,
  read its key and call delete. Work `O((count-n)*key_len)`; no extra log.
- `htab_item(t,ordinal)`: `leaf = HT_ORDER[ordinal]`, return
  `<1, key_ptr(leaf), value(leaf)>`; `htab_slot` is the leaf-id variant.
- `htab_keys`: copy `HT_ORDER` entries at stride, unchanged.
- `htab_union_into`: unchanged, now `O(|src|*key_len)`.
- `htab_copy`: copy header, key arena, values, order, order_pos, internal node
  pool, and free-list heads; scratch version uses `scratch_alloc`.

### Deterministic worst-case cost

For a lookup: `8*key_len` bit reads + one `key_len`-byte compare.
For insert/delete: `8*key_len` + `key_len` + constant.
No probe chain and no `capacity` factor. In particular the adversarial
20-byte family `BE64(n)||BE64(n)||zero32` cannot collide: Patricia branches on
the first differing bit, so each key is a separate leaf at depth <= 160.

## 3. Memory bound

For `n = HT_CAP`, `stride = (key_len+7)&-8`:

```
header                 104 bytes
key arena              n*stride
values                 n*8
order                  n*8
order positions        n*8
internal nodes         (n/2)*24
free-list storage      reused from values/nodes
------------------------------------------
total                  n*(stride + 36) + 104 bytes
```

Examples:

| key_len | stride | bytes/entry | current hash table bytes/entry |
|---|---|---|---|
| 20 | 24 | 60 | 49 |
| 32 | 32 | 68 | 57 |
| 52 | 56 | 92 | 81 |

The replacement is 1.14x-1.22x the current table footprint, not asymptotically
larger. For the 32-byte node-DB path at `n = 2^26`, that is about 4.56 GB of
sparse arena (3.76 GB key/value/order + 0.81 GB internal nodes), versus 3.83 GB
for the current table. If the arena limit is tighter, the internal node can be
packed to 16 bytes (`child0`, `child1`, `u16 bit`, `u16 flags`) without changing
the algorithm, reducing this to `n*(stride+32)+104` (about 4.29 GB).

## 4. Certificate integration plan

1. Add a participant-only `htab` module replacing only `lib/htab.pnk` in the
   candidate source tree; preserve header offsets 0/8/16/24 and all API names.
2. Prove/store the data-structure invariant as a reachable Patricia tree:
   - every internal node has strictly increasing bit indices on every path;
   - every live leaf is reachable exactly once and all leaves have distinct
     `key_len`-byte keys;
   - `HT_ORDER` is a permutation of live leaf ids and `HT_ORDER_POS` its
     inverse; `HT_COUNT` is its length.
3. Per-operation source traces: lookup visits at most `8*key_len+1` nodes and
   compares `key_len` bytes once; insert/delete add one bounded first-diff scan
   and O(1) pointer/order updates. These are concrete `StatementRun` events
   under the existing source-price API, so the certificate gets a
   `C_table(key_len)` per operation rather than a capacity-linear bound.
4. Replace `HtabSetBound`/`NodedbBodyBound` capacity-linear `setBodyCost` with
   `lookupCost = a*key_len + b`, `updateCost = c*key_len + d`; then
   `nodedbBodyCost(count) = O(count*key_len)`, not `O(count*capacity)` and not
   input-quadratic. At 32-byte keys this makes the full-input database bound
   linear in the entry count.
5. Keep `htab_union_into` in `state.pnk` unchanged; it remains O(|src|*key_len).
6. Re-run the same adversarial family test: all keys become separate leaves;
   repeated warm lookups are `O(key_len)`, independent of cluster size.

## 5. Prototype

`prototype.py` is a deterministic executable model of the Patricia map with the
same insertion-order/swap-remove/truncate semantics. It is randomized against a
reference ordered map and reports the maximum number of node visits and
key-byte comparisons per operation. This validates the indexing/order/deletion
logic before writing the PNK candidate.

## 6. Candidate source, parser/type check, and checked invariant

- `htab_patricia.pnk` is the isolated participant-only API-compatible candidate.
  It keeps header offsets 0/8/16/24 and every entry point used by clients. It is
  not wired into `guest/` or any build.
- `compile_check.sh` preprocesses a minimal `main` that allocates a table and
  exercises set/get/item/del/truncate, then runs
  `lake exe flapjack-compile --assembly`. This passes the Pancake parser and
  type checker for the candidate. The PNK form avoids `/`, nested call
  arguments, and calls in conditions, which the parser does not accept.
- `PatriciaInvariant.lean` is checked with `lake env lean`. It proves for any
  Patricia shape:
  - `nodes t = 2 * leaves t - 1` (Nat), hence `nodes t ≤ 2 * leaves t`;
  - if all branch bits lie strictly in `(0, 8*key_len)`, then
    `depth t ≤ 8*key_len`.
  The `Between` predicate is exactly the strictly increasing-bit-index
  invariant required by insertion/deletion. Axioms are only `propext` and
  `Quot.sound`.
- `prototype.py` is the executable semantic/capacity model. It passed
  randomized operations for key lengths 20, 28, 32, 52, and 60 against a
  reference ordered map, including exact insertion-order and swap-remove
  equality. It also checks `live_internal <= cap/2` after every operation and
  passed the 5,000-key adversarial family for 20/32/60-byte keys.
- `differential_spike.sh` is the linked differential harness: it compiles the
  candidate PNK to RISC-V ELF, runs it on Spike, and compares the guest-written
  checksum with `prototype.py`. It passes at N=200 and N=5000, including
  growth, 1,000 explicit deletions, and a truncate to N/4.

## 7. Measured operation counts; what is still unproved

The 5,000-operation randomized runs (seed = key length) and 5,000-key
adversarial runs produce deterministic counters, not a source-cost proof:

| case | max visits | live internals / cap | grows | copy moves |
|---|---|---|---|---|
| random L=20 | 8 | 28 / 64 | 3 | 28 |
| random L=32 | 8 | 31 / 64 | 3 | 28 |
| random L=52 | 8 | 33 / 128 | 4 | 60 |
| random L=60 | 7 | 30 / 64 | 3 | 28 |
| adversarial L=20 | 13 | 4999 / 16384 | 11 | 8188 |
| adversarial L=32 | 13 | 4999 / 16384 | 11 | 8188 |
| adversarial L=60 | 13 | 4999 / 16384 | 11 | 8188 |

Amortization that must be in the certificate, not assumed away:

- `htab_grow` doubles capacity and rebuilds from `HT_ORDER`; the sum of moved
  entries over all doublings is at most `2N`, so growth adds an amortized
  `O(key_len)` per insert. The measured 8,188 moves for N=5,000 is below the
  `2N=10,000` bound.
- `htab_copy` remains `O(cap + nodes)` because it copies arrays and nodes. It is
  invoked once per block in `compute_state_root`, not per transaction; its cost
  must be charged once against the block-level independent term.
- `htab_truncate(t,n)` performs `count-n` real deletions, each `O(key_len)`.
  These deletions are charged exactly once; there is no hidden O(N) scan.
- `order`/`order_pos` update in O(1) per insert/delete; deletion uses the same
  swap-remove semantics as the old table.
- The 60-byte case has `8*60=480` maximum branch depth; the invariant bounds
  this without a per-key length assumption other than `key_len ≤ 60`.

The earlier `3.4e11` figure was a projection, not a proof. What is established
now is structural: lookup is `O(key_len)` nodes and one `key_len` compare;
insert/delete/truncate are `O(key_len)` plus the counted order/growth work; the
pool is `≤2N` nodes and `N ≤ cap/2`. The actual executed source ticks per op
still need to be derived from the generated `StatementRun` events and the
coefficients of the source-price API.

## 8. Linked Spike differential and executed step counts

`N=5000 differential_spike.sh` runs the isolated PNK candidate as a bare-metal
Spike guest. The guest writes `sum(values) + count` to `OUTPUT_ADDR`; the model
computes the same sequence. All checksums match:

| phase | sequence | Spike steps | checksum |
|---|---|---|---|
| 0 | 5,000 inserts, final 5,000-entry iteration | 38,004,620 | match |
| 1 | phase 0 + 1,000 deletes | 40,995,787 | match |
| 2 | phase 1 + truncate 5,000 -> 1,250 | 48,123,994 | match |

Phase deltas give actual executed machine-step costs for the bookkeeping the
lead asked to charge explicitly:

- 1,000 explicit deletes: `2,991,167` steps, about `2,991` steps/delete.
- 3,750 truncation deletes: `7,128,207` steps, about `1,901` steps/delete
  (the trie is smaller after truncation, so this is not a lower bound for the
  deep case; it is the actual measured phase).
- 5,000 inserts with 6 growths plus one 5,000-item iteration: `38,004,620`
  steps total, including all resize/rebuild work.
- Growth/rebuild totals are already included in phase 0; no O(N) scan is hidden
  outside the measured phases.

These are Spike machine steps, not yet the source-price `WorkEvent` ticks used
by the certificate. They establish that the compiled candidate has the claimed
behavior and give a calibration path for the source-event derivation; they do
not by themselves prove the `9e11` bound. The step counts scale sub-quadratically
at these sizes, but the asymptotic certificate still needs the per-operation
`StatementRun` events and coefficient calibration.

## 9. Reachable order/ownership invariant and key-length coverage

`ReachableOrderInvariant.lean` is checked with `lake env lean` and proves the
concrete bookkeeping that the shape-only depth lemma did not cover:

- `swapRemove_perm_erase`: the exact replacement-of-position-`i`-by-last-order
  update is a permutation of ordinary erasure of the key at position `i`,
  assuming the order list is duplicate-free. This is the PNK `htab_del`
  order update, including the last-position case.
- `Ordered.insert`: appending a new leaf preserves `order ~ live`.
- `Ordered.delete`: swap-removal preserves `order ~ live.erase x`.
- `Owned.alloc` / `Owned.free`: with the pool partition invariant
  `(live ++ free) ~ pool` and `pool.Nodup`, moving one id from `free` to `live`
  and back preserves the partition. This is pool recycling, disjointness, and
  the `live.length + free.length = cap` accounting in permutation form.

Axioms printed for the file are only `propext`, `Classical.choice`, and
`Quot.sound`.

Linked Spike/model checks now cover the database key sizes as well:

| N | key length | Spike steps | checksum |
|---|---|---:|---|
| 1,000 | 20 | 6,355,778 | match |
| 1,000 | 32 | 6,390,582 | match |
| 1,000 | 60 | 6,905,554 | match |
| 5,000 | 20 | 48,123,994 | match |
| 5,000 | 32 | 48,449,122 | match |
| 5,000 | 60 | 51,222,010 | match |

The 32-byte case is the node-DB shape; 60 bytes is the maximum key length used
by the guest. No resize/copy/truncate path is bypassed in these runs.

## 10. Pinned compile/source record

- candidate source: `submission/BoundedTableExperiment/htab_patricia.pnk`
  sha256 `7c10739a25f47721672c56de0e890e9167e88e177489f8dac91639050a482ae7`
- semantic model: `submission/BoundedTableExperiment/prototype.py`
  sha256 `ad8b1bdea4186f3da088bea6a6c421e9745cca1fb74c49a1affc5ef83edce64d`
- order/ownership proof: `ReachableOrderInvariant.lean`
  sha256 `9692b073524d5b3abe3e9d30f3dbaa4ede999ac5f0351379aa0658bb6bbe7342`
- preprocess: `cpp -P -w -nostdinc -I guest/src -x c`
- compiler: `lake exe flapjack-compile --assembly`, Flapjack revision
  `034bb5a1ed0b757082768d5406206bd2f8e31b7c` from `lakefile.toml`
- RISC-V execution: `tools/spike/spike_run`, built from
  `riscv-isa-sim` with `riscv64-unknown-elf-{as,ld}`

These are experimental participant artifacts, not challenge inputs.

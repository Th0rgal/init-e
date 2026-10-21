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
- `CapOwned` specializes the pool to the concrete id list `1..cap` and proves
  the exact count `live.length + free.length = cap` plus the range facts
  `1 <= x <= cap` for every live and free id. This is the concrete capacity
  and no-out-of-range-id invariant, not just a generic permutation.

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
  sha256 `a97b7463d8f5371a33b92b3f16974f1c8e799bec1c13b71b1c95144b664b7669`
- semantic model: `submission/BoundedTableExperiment/prototype.py`
  sha256 `ad8b1bdea4186f3da088bea6a6c421e9745cca1fb74c49a1affc5ef83edce64d`
- order/ownership proof: `ReachableOrderInvariant.lean`
  sha256 `9b8dba5090f7c5fffe16dc0f6875d7087e5652408e7f30ca5ff38025f683160b`
- preprocess: `cpp -P -w -nostdinc -I guest/src -x c`
- compiler: `lake exe flapjack-compile --assembly`, Flapjack revision
  `034bb5a1ed0b757082768d5406206bd2f8e31b7c` from `lakefile.toml`
- RISC-V execution: `tools/spike/spike_run`, built from
  `riscv-isa-sim` with `riscv64-unknown-elf-{as,ld}`

These are experimental participant artifacts, not challenge inputs.

## 11. Lifecycle, copy/scratch, and remaining key lengths

`lifecycle_spike.sh` runs a linked test with 200 inserts, `htab_copy`,
`htab_copy_scratch`, mutation of both copies, 100 deletes, 100 reinserts across
the growth boundary, and 50 delete/reinsert recycling cycles. It verifies that
the original and copies are independent and that every live/dead lookup is
correct. Result: `1,641,719` Spike steps, status/count checksum `1,000,200`,
matching the expected `1e6*ok + count`.

`copy_spike.sh` measures copy cost directly by comparing `COPIES=0` with
`COPIES=1` at N=5,000:

| operation | Spike steps | delta | per entry |
|---|---:|---:|---:|
| no copy | 37,514,634 | — | — |
| heap `htab_copy` | 38,037,709 | 523,075 | ≈105 |
| scratch `htab_copy_scratch` | 38,037,661 | 523,027 | ≈105 |

Thus a copy is linear in the table and must be charged once per block where
`compute_state_root` invokes it; it is not hidden in the per-lookup path.
Scratch copy has the same measured cost and its allocations are released with
the frame.

The remaining key lengths are now linked-tested too:

| N | key length | Spike steps | checksum |
|---|---|---:|---|
| 1,000 | 28 | 6,537,347 | match |
| 1,000 | 52 | 6,747,606 | match |

All of these are Spike machine steps, not source-price ticks; the certificate
still needs the generated `StatementRun` events and coefficient calibration.

## 12. Worst-depth path test and exact visit accounting

`worstpath_spike.sh` inserts one key per bit position (key `j` has only bit `j`
set) in MSB-first order. This forces the Patricia spine to its deterministic
depth, then repeats all lookups 100 times.

| key length | keys | max visits | all-key steps | result |
|---|---:|---:|---:|---|
| 20 | 160 | 159 | 25,125,926 | match |
| 32 | 256 | 255 | 58,245,738 | match |
| 60 | 480 | 479 | 198,184,285 | match |

The max visits are exactly `8*key_len - 1`. However, dividing the all-key time
by `keys * repeats * max_depth` is wrong: the spine keys have mixed depths.
For KL32 the model's exact total is 32,895 visits per 256-key cycle, mean depth
128.496; 100 cycles are 3,289,500 visits. Subtracting the 256-insert baseline
(1,478,654 steps), the whole-spine coefficient is
`56,767,084 / 3,289,500 = 17.26` steps per visited node.

`deepest_spike.sh` isolates the true maximum path. It builds the same spine and
repeats only key bit 254:

| run | steps |
|---|---:|
| REPEAT=0 (build only) | 1,478,654 |
| REPEAT=10,000 | 42,628,655 |

Delta `41,150,001 / 10,000 = 4,115.0` steps per lookup at depth 255, i.e.
`16.14` steps per visited node. The earlier `13.2/visit` figure used a
maximum-depth denominator over a mixed-depth workload and undercounted by about
2x; the corrected deepest-path coefficient is 16.14.

## 13. Direct node pointers and route encoding

The current candidate removes the remaining per-hop id-to-address arithmetic:

- internal child ids are actual node pointers; leaf ids stay `<= cap`, so
  `node <= cap` still identifies a leaf, while internal pointers are heap
  addresses `> cap`;
- the internal free list stores pointers; `htab_new_internal` and
  `htab_free_internal` no longer call `htab_node_ptr`;
- growth and copy relocate every internal pointer by `newbase - oldbase`;
- routing is encoded as `byte_offset*256 + (255 - mask)`, so a node stores a
  route that is monotone in the bit index. Lookup does
  `ld8 (key + (route >> 8)) & (route ^ 255)` with no variable shift or bit
  index extraction. `htab_first_diff` returns the same encoded route.

Measured deepest-leaf lookup: `4,625` steps before route encoding, `4,115`
after; per visit 18.14 -> 16.14. Whole-spine KL20/32/60 steps are
25,125,926 / 58,245,738 / 198,184,285. All 20/28/32/52/60 differential
checksums, lifecycle copies, deletes, and truncates still match.

## 14. Structural growth (no re-insertion walk)

`htab_grow` no longer re-inserts every key. It allocates the doubled table,
copies the old arrays, relocates the internal-node slab and pointer free list
by `newbase - oldbase`, rebuilds the extra internal and leaf free lists, remaps
the root, and copies the header. The work is O(cap) memory movement rather than
O(count * key_length * depth). Leaf ids and order arrays are unchanged.

The linked tests match after every optimization stage:
- N=5,000 KL=32: 16,577,066 (bulk growth) -> 13,064,208 (direct pointers) ->
  12,721,381 (route encoding) -> 12,428,351 (single-descent insertion).
- Lifecycle copy/delete/reinsert: 837,997 -> 711,407 -> 698,546.
- Copy at N=5,000: 670,581 delta, ~134/entry (pointer relocation included).

## 15. Single-descent insertion

The previous `htab_set` walked root-to-leaf, computed the first differing route,
then walked root-to-leaf again to find the split point. The candidate now keeps
a reusable path buffer in the table header (`HT_PATH`, `HT_DEPTH`, sized
`key_len*64` bytes). The descent records each internal node; after `d` is known,
a binary search over the strictly increasing path routes finds the split point,
and one final key-byte load determines the child direction. No second
root-to-leaf walk remains.

Measured effect on the 256-key spine build (all inserts, no lookups):
1,478,654 -> 1,021,083 steps, a 1.45x reduction. Deepest-leaf lookup is
unchanged at 4,115 steps.

## 16. Corrected conservative budget

Using the measured KL32 deepest-path coefficient 16.14 steps/visited node and
the measured one-walk insertion:

- new-key insert: one 255-hop walk (`~4,116`) plus path stores, binary search,
  key compare, and split-link work; budget conservatively 4,500 steps;
- `33.55M * 4,500 = 1.51e11`;
- one deepest read per input entry: `33.55M * 4,115 = 1.38e11`;
- subtotal `2.89e11`;
- copy: `~4.5e9` (measured 670,597 delta at N=5,000, ~134/entry);
- structural growth: `~1e10` or less;
- total before nodedb/transcript/other guest work: `~3.0e11`.

This is below `9e11` with roughly 3x margin. It remains a measurement-based
projection, not a proof: it assumes at most one insert plus one read of table
work per input entry, and it does not include the source-tick/native-step ratio
or the real full-input operation mix. The adversarial depth-256 shape, exact
model visit totals, and deepest-leaf-only measurement are now recorded.


## 17. Pointer/slab refinement for the final representation

`ReachableOrderInvariant.lean` now also checks the arithmetic core of the
final direct-pointer representation:

- `slab base cap = [base + 24*i | i < cap/2]` is duplicate-free; every member
  has the form `base + 24*i` with `i < cap/2`.
- `PtrOwned base cap live free` is the slab instantiation of the pool
  partition. It preserves `live.length + free.length = cap/2` and
  `Owned.alloc`/`Owned.free`.
- If `cap < base`, every live or free internal pointer is `> cap`, so the
  `node <= cap` leaf test remains unambiguous.
- Relocation maps `x` in `slab base cap` to `x + delta` in
  `slab (base+delta) cap`; if the slab end plus delta is below `2^64`, the
  relocated pointer does not exceed the address space.
- `regions_disjoint`: two half-open address regions with non-overlapping
  bounds share no address. This is the heap/scratch separation obligation.

Scope: this is a checked arithmetic/ownership refinement of the pointer
representation, not yet a full heap-memory refinement of the PNK code. The
16.14-step/visit figure is a native Spike diagnostic; the source-event price of
the hotspot loop has not been extracted, so the ~3x budget margin is deliberate
and the projected score remains unproved.


## 18. Frozen checkpoint, path-buffer specification, and calibration handoff

Algorithm optimization is frozen at the tested candidate with source hash
`a97b7463...` (commit `fe3f284d2`). Further work is proof/calibration only.

`PathInvariant.lean` checks the path-buffer split specification:

- `splitIndex path d` is the number of recorded routes `<= d`;
- every route before the split is `<= d`;
- in a strictly increasing path, every route at or after the split is `> d`;
- `strict_snoc` preserves strict route monotonicity when a new route larger
  than all existing routes is appended.

The executable binary search is the implementation of this specification; the
current proof establishes the specification, not a mechanized
binary-search-to-spec refinement. `ReachableOrderInvariant.lean` supplies the
arithmetic region-disjointness lemma for the path buffer versus
keys/nodes/output/scratch, but the heap allocator's liveness/reuse refinement
for `HT_PATH` is still open.

For source-cost calibration, the concrete trace model should emit, per
operation: op kind, key length, table count/cap, path depth, node visits,
path-buffer stores, binary-search steps, key-compare bytes, child-link writes,
copies/growth bytes, and output writes. The existing `prototype.py` counters
already provide most of these; the missing piece is the exact preIsel/source
price per event. Until that is supplied, the 16.14 native steps/visit and
~3e11 projection remain diagnostics, not the budget theorem.

## 19. Concrete operation trace for source-price calibration

`prototype.py` now records `path_stores`, `bsearch_steps`, and `link_writes`
alongside the existing visit/compare/order/copy counters. `trace_model.py`
emits one JSON event per operation with the deltas of every counter plus
`op`, key index, `cap`, and `count`. The canonical run has 1,477 events
(1,000 inserts, 334 deletes, 143 gets) with totals
`path_stores=7,456`, `bsearch_steps=2,774`, `copy_moves=1,020`.  The model's
growth is now structural (capacity doubles without re-inserting keys), matching
the frozen candidate; this changes the trace counts but not the checksum
semantics.

This is the concrete trace model requested for source-price calibration. It is
a behavior/count trace, not a source-event trace; an exact preIsel/source price
per event still needs to be supplied. The optimized candidate remains frozen at
`fe3f284d2` / source hash `a97b7463...`.

## 20. Frontend-only source prices and duplicate/fresh composition

`price-harness/` compiles the frozen candidate AST through the frontend to
Loop→Word with plain `lean --run` and the fleet shared oleans. It prices one
executed loop body at `preX` and at the optimized stages. Per-body diagnostic
prices (`preX` / after `removeDead`):

| function | label | per internal visit/step |
|---|---:|---:|
| `htab_find_leaf` | 103 | 816 / 723 |
| `htab_find_leaf_path` | 104 | 1080 / 1107 |
| `htab_set` binary search | 109 | 590 / 592 |
| `htab_grow` | 108 | 1464 / 1611 |
| `htab_truncate` | 111 | 874 / 1307 |
| `htab_relocate` | 107 | 1152 / 1203 |
| `htab_del` descent | 110 | 891 / 1614 |

`budget_model.py` separates duplicate updates from fresh inserts:

- duplicate update: one path-descent, no binary search and no allocation;
- fresh insert: path-descent + binary search + one new leaf/internal pair +
  amortized relocation of at most two internal nodes per leaf + one growth
  loop body.

At 33,550,000 entries, using the optimized prices and average depth 8:

| duplicate fraction | total source units | per entry |
|---:|---:|---:|
| 0% | 5.11e11 | 15,241 |
| 90% | 3.19e11 | 9,494 |
| 99% | 2.99e11 | 8,920 |
| 99.9% | 2.97e11 | 8,862 |

The duplicate term dominates. At depth 8 even 99.9% duplicates consume about
2.97e11 source units, above the ~2e11 remaining budget. At depth 4 and 90%
duplicates the total is 1.68e11, which fits. Therefore a finite composition
requires a proved bound on average live path depth or on total table
operations, not just a bound on distinct keys; fresh-insert count still uses
`min(entries, input_bytes / min_key_len)`.

These are diagnostics from `preX`/`optP`, not the score theorem. Truncation
adds one delete descent (110) plus one truncate body (111) per removed entry;
the model includes those prices but not a specific truncation count.

## 21. Distinct-key coupling and the depth budget

A Patricia tree with `K` live leaves has average depth at most
`min(8*key_len, K-1)` (the comb is the worst shape). Table operations `M` all
pay that average depth, so the descent term scales with `K`, not `M`.

At `M = 33,550,000`, `key_len = 4`, optimized prices, worst-case comb depth:

| distinct keys K | avg depth bound | total source units |
|---:|---:|---:|
| 2 | 1 | 3.71e10 |
| 4 | 3 | 1.11e11 |
| 6 | 5 | 1.86e11 |
| 8 | 7 | 2.60e11 |
| 16 | 15 | 5.57e11 |
| 32 | 31 | 1.15e12 |

Thus with the current per-visit prices, at most about six distinct live keys
fit the ~2e11 remainder; eight already exceed it. The byte/unique coupling
`K <= input_bytes / min_key_len` does not rescue this: 134MB of 4-byte keys
still permits 33M distinct keys.

This is the key open budget obstruction. A finite composition needs either a
proved much smaller average live path depth for the reachable nodedb keys, a
proved operation-count bound, or a cheaper per-visit source path. No finite
claim is made from these diagnostics.

## 22. Break-even operation count against the 2e11 remainder

`budget_model.py ... 200000000000 max` gives the maximum number of table
operations that fit 2e11 source units at a given average depth:

| avg depth | 0% dup | 90% dup | 99% dup | 99.9% dup |
|---:|---:|---:|---:|---:|
| 1 | 35.0M | 127.6M | 173.4M | 179.9M |
| 2 | 27.0M | 73.2M | 88.3M | 90.1M |
| 4 | 19.6M | 39.9M | 44.6M | 45.1M |
| 8 | 13.1M | 21.1M | 22.4M | 22.6M |
| 16 | 8.1M | 10.9M | 11.2M | 11.3M |
| 25 | 5.8M | 7.0M | 7.2M | 7.2M |

At the 33.55M entry bound, the table fits only with average depth at most 4
(90%+ duplicates) or depth 1–2 with fewer duplicates. At depth 8 the break-even
count is about 21M, so either the reachable operation count must be bounded
below 33.55M or the average path depth must be proved small. These are
diagnostics, not the score theorem.

## 23. Path split uniqueness (checked)

`PathInvariant.lean` now proves `splitIndex_eq_of_take_drop`: for a strictly
increasing path, any index whose prefix routes are `<= d` and whose suffix
routes are `> d` must equal `splitIndex`. Axioms are only `propext` and
`Quot.sound`. `bsearchList` is the recursive divide-and-conquer form of the
loop; executable checks on several paths return the same index as
`splitIndex`. The iterative loop-to-`splitIndex` refinement is still not
mechanized.

## 24. Checked growth-copy amortization

`GrowthBudget.lean` proves that for structural capacity doubling, the total
capacity moved over all growths is at most the final capacity:

- `capSum base n <= base * 2^n` (`capSum_le_final`);
- hence a single growth moves at most twice the old live capacity
  (`capSum_succ_le_two_mul_final`).

Axioms are only `propext` and `Quot.sound`. Truncation does not shrink capacity
and performs no array copy; each removal pays one delete descent plus one
swap-remove/truncate body. So resize/copy is amortized O(1) per fresh insert in
capacity units (source price per relocated node is the measured 1203; the
memcpy-per-byte price remains unpriced).

## 25. memcpy and growth-copy source price

The candidate's `memcpy` (label 76) has a 32-byte loop body priced at
`preX = 426`, `removeDead optP = 2333`, i.e. about 73 source units per byte.
`memzero` (77) is 1373 per body; `memeq` (78) is 945 per body; `alloc` (67) is
1022.

With `capSum_le_final`, total copied array bytes over all growths are at most
`final_cap * row_bytes`, where `row_bytes = key_stride + 24` (key, value,
order, and position arrays; 56 for a 32-byte stride). Adding this term to the
fresh-insert cost lowers the 2e11 break-even counts:

| avg depth | 90% dup | 99% dup |
|---:|---:|---:|
| 4 | 36.9M | 44.2M |
| 8 | 20.2M | 22.3M |
| 16 | 10.6M | 11.2M |

The duplicate term still dominates the obstruction; fresh inserts additionally
pay about `row_bytes * 73` source units of amortized array copying.

## 26. Trace-to-PNK event relation

`trace_relation.py` checks every model event against the PNK operation shape:

- `set_new`: one path descent, `path_stores` recorded nodes, at most
  `ceil(log2(depth+1))` binary-search steps, one child-link write (zero for the
  first root leaf); a growth event performs a second descent after relocation,
  so `visits = 2 * path_stores`;
- `set_update`: descent only, no path stores, search, or link write;
- `get`: descent only;
- `delete`: at most one swap-remove order move.

The 1,477-event canonical trace passes with zero failures. This is a behavioral
trace-to-PNK relation, not a proof of the PNK heap semantics.

## 27. Iterative binary-search refinement (checked)

`BinarySearchRefinement.lean` models the PNK loop's `lo/hi/mid` state and
proves:

- `step_split`: if `lo <= S <= hi` and `S` is the unique split point
  (`i < S ↔ routes i <= d`), one loop step keeps `lo <= S <= hi`;
- `step_gap`: an entering step strictly decreases `hi - lo`;
- `run_split`: with fuel at least `hi - lo`, the loop terminates with
  `lo = S`.

Axioms are only `propext` and `Quot.sound`. This refines the iterative loop to
the split specification; tying the specification to the concrete `HT_PATH`
list via `getD` membership is the remaining glue.

## 28. Concrete path-buffer heap footprint (checked)

`HeapFootprint.lean` defines half-open region containment/disjointness and
proves:

- `path_store_in_region`: a store at `path + depth*8` lies inside a path buffer
  of at least `(depth+1)*8` bytes;
- `path_read_in_region`: a binary-search read at `mid < depth` lies inside the
  recorded path;
- `path_store_no_alias`: path stores cannot overlap one other region;
- `path_store_no_alias_all`: under `PathSafe` (path disjoint from keys, nodes,
  output, and scratch), the store address is in none of those four regions.

Axioms are only `propext` and `Quot.sound`. These are concrete pointer/offset
lemmas; allocator liveness and the actual PNK statement-run cost coupling are
still open.

## 29. Concrete path memory refinement (checked)

`BinarySearchRefinement.lean` now also models word-addressed memory:

- `pathAt m base i = m (base + i*8)` is the concrete load for abstract path
  slot `i`; `pathList` maps a range of slots to those loads;
- `pathList_getD` proves the abstract `getD` read is exactly `pathAt`;
- `path_store_in` proves a path store lies in the path region;
- `path_store_not_other` and `path_store_other_load` prove a store into the
  path region does not change loads in any disjoint region;
- `path_store_old_slot` / `path_store_new_slot` prove earlier slots are
  preserved and the new slot reads back;
- `run_split_path` instantiates the iterative binary-search refinement with
  concrete path-memory loads.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. This ties the abstract
`getD`/split spec to loads/stores and disjoint footprints; actual PNK
statement-run cost coupling remains open.

## 30. Path store coupled to the actual `StatementRun`

`PathStatementCoupling.lean` imports the candidate runtime's
`InitECandidate.Runtime.PanStatementWork` (cached oleans, no source build) and
proves:

- `storeValue_events`: the actual `StatementRun.storeValue` rule emits
  `.statement`, then the address/value expression events, then
  `.memory (flattenHOL value).length` and
  `.cost (storeOverhead (flattenHOL value).length)`;
- `path_store_one_word_events`: for a one-word stored value this is a real
  `StatementRun` whose event list contains exactly one `.memory 1` and the
  one-word native store cost;
- `path_store_one_word_units`: those events charge one memory access and
  `storeOverhead 1` native units.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. This is statement-run
event coupling for the path store; coupling the loop guard/load executions and
the full per-operation cost remains open.

## 31. Path-load / loop-guard expression coupling

`PathStatementCoupling.lean` also proves:

- `path_load_expression_events`: every path-load or loop-guard expression has
  the actual `CostedExpressionRun` with event list `[.cost (sourcePrice s e)]`;
- `path_load_expression_cost`: that run charges exactly
  `nativeCost * sourcePrice s e`;
- `path_load_has_cost_event`: the native-price event is present.

So the path buffer's load/guard executions are coupled to the candidate
expression cost, not just counted by the model. Axioms are `propext` and
`Quot.sound` for the cost lemmas.

## 32. Full one-word path-store statement-run score

`path_store_one_word_score` composes the actual store trace with the work
coefficients:

```
score = statements
      + score(addressEvents) + score(valueEvents)
      + memoryAccesses + nativeCost * storeOverhead 1
```

The two expression runs are the actual `CostedExpressionRun`s from section 31.
Axioms are `propext`, `Classical.choice`, `Quot.sound`. This is the full
statement-run cost of one path slot store; composing several slots and the
binary-search load loop remains open.

## 33. Multi-slot path-store score composition

`PathStatementCoupling.lean` adds:

- `path_stores_score_append`: concatenated path-slot traces add scores;
- `path_stores_score`: the score of a flat list of slot traces is the sum of
  the per-trace scores;
- `n_path_slots_score`: `n` one-word slots charge
  `n * (statements + memoryAccesses + nativeCost * storeOverhead 1)`.

Axioms are `propext` and `Quot.sound` for the composition lemmas. This composes
the path push across slots; composing with the binary-search load loop into the
whole operation still needs the loop-level event trace.

## 34. Actual while-iteration event composition

`PathStatementCoupling.lean` adds the actual `StatementRun.whileNext` rule:

- `whileNext_events`: one executed loop iteration emits `.statement`,
  `.cost (whileOverhead + loopMoves fn)`, then the guard expression events,
  body events, and the remaining loop events;
- `whileNext_score`: its score is

  ```
  statements + nativeCost*(whileOverhead + loopMoves fn)
    + score(guardEvents) + score(bodyEvents) + score(restEvents)
  ```

Axioms are `propext`, `Classical.choice`, `Quot.sound`. Combined with the
multi-slot store score, a path-push loop body can now be costed from executed
statements; instantiating guard/body events for the concrete `htab_set` loop is
the remaining step.

## 35. N-iteration loop event trace score

`PathStatementCoupling.lean` adds:

- `whileIterationEvents` / `whileIterationEvents_score`: one loop iteration
  trace (`statement`, overhead, guard events, body events) scores as the sum of
  its parts;
- `n_while_iterations_score`: `n` identical iterations score
  `n * (statements + nativeCost*overhead + score(guard) + score(body))`;
- `n_guard_slot_iterations_score`: a guard costing `nativeCost*guardPrice`
  plus one one-word path-slot store per iteration scores
  `n * (statements + nativeCost*overhead + nativeCost*guardPrice
       + statements + memoryAccesses + nativeCost*storeOverhead 1)`.

Axioms are `propext` and `Quot.sound`. This is the loop-level event-trace
composition; binding the concrete `htab_set` guard prices and link write is
the remaining instantiation.

## 36. Actual candidate `StatementRun` traces and costs

`CandidateStatementRuns.lean` imports the generated candidate AST
(`Candidate.guestFn_*`, the exact PNK program, not a surrogate model) and the
runtime's `source_evaluation_cost_trace` / `sourceExecutionCost_spec`:

- `candidate_htab_set_trace` / `candidate_htab_set_cost_spec`: the actual
  `htab_set` body has a finite size-aware `StatementRun` from every state, and
  the selected trace's source cost equals `sourceExecutionCost`;
- the same for `htab_find_leaf_path`, `htab_del`, `htab_truncate`, `htab_grow`,
  `htab_copy`, and the whole `main`.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. These are existence and
cost-consistency results for the actual candidate AST. They do not yet give a
closed per-operation cost formula or the Patricia heap/path invariants; the
binary-search/path-push/link event decomposition still has to be proved by
case analysis on the candidate AST and its actual semantics.

## 37. Actual PNK one-word store frame

`ActualPathStoreFrame.lean` uses the runtime's actual `panMemStoresHOL_frame`:

- `actual_one_word_store_frame`: an actual one-word PNK store leaves every
  different watched cell unchanged;
- `actual_storeValue_frame`: the post-memory of an actual
  `StatementRun.storeValue` with a one-word value is unchanged at every watched
  cell other than the store address.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. This is the actual
memory-semantics preservation half of the path-store invariant; it still needs
to be instantiated at the candidate's concrete path addresses and combined with
the search/push/link run decomposition.

## 38. Actual path-memory push invariant

`ActualPathMemoryInvariant.lean` defines the concrete path slot address
`pathAddr base i = base + 8*i` and the actual-state invariant
`PathMemoryInv s base depth routes`: every slot below `depth` holds its route
word in `s.memory`.

`PathMemoryInv.push` proves that an actual one-word `panMemStoresHOL` at
`pathAddr base depth` extends the invariant to depth `+1`, provided the slot is
in the address domain and `depth < 2^61`:

- old slots are unchanged by `actual_one_word_store_frame`;
- the new slot reads back the stored route via `panMemStoreHOL_hit`.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. This is an actual PNK
heap/path preservation lemma; it is not yet connected to a full `htab_set` run
decomposition.

## 39. Actual Patricia link-write invariants

`ActualLinkMemoryInvariant.lean` defines `NodeLinkInv s node left right route`
for a 24-byte internal node: memory at `node`, `node+8`, `node+16` holds the
left child, right child, and route words. It proves:

- `NodeLinkInv.setLeft`: an actual one-word `panMemStoresHOL` at `node`
  updates the left child and preserves the right child and route;
- `NodeLinkInv.setRight`: an actual one-word store at `node+8` updates the
  right child and preserves the left child and route.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. These are actual
semantics link-write preservation lemmas; linking them into the full
`htab_set` run remains open.

## 40. Path invariant framing under outside stores

`PathMemoryInv.store_other` proves that an actual one-word store at any address
outside every recorded path slot leaves `PathMemoryInv s base depth routes`
unchanged. This is the framing half needed when `htab_set` writes nodes, key
bytes, or table arrays while the path buffer remains live.

Axioms are `propext`, `Classical.choice`, `Quot.sound`.

## 41. Link invariant framing under outside stores

`NodeLinkInv.store_other` proves that an actual one-word store at an address
outside `node`, `node+8`, and `node+16` preserves the node's left/right/route
words. This lets a path-buffer push be framed against the live node links.

Axioms are `propext`, `Classical.choice`, `Quot.sound`.

## 42. Actual candidate `htab_set` top-level AST decomposition

`CandidateSetShape.lean` proves the exact candidate AST reduces through the
runtime codec:

- `sourceFunctionBody_function` and `candidateHtabSet_body`: the body is a
  `dec "cap"` scope;
- `candidateHtabSet_body_seq`: its scope body is a two-arm `seq`;
- `candidateHtabSet_miss_eq`: the first arm is the root-empty `ite`;
- `candidateHtabSet_found_eq`: the second arm is the
  `decCall "leaf" htab_find_leaf_path` call;
- `candidateHtabSet_body_branches`: the combined top-level shape.

`declareValue_score` and `ite_score` give the actual statement-run event
scores for the declaration and branch constructs. Axioms are `propext`,
`Classical.choice`, `Quot.sound`.

This is actual AST structure, not an abstract model. The nested search loop,
path push, binary search, and link write inside `htab_find_leaf_path` and
`candidateHtabSetLeafBody` still need the same peeling and `StatementRun`
composition.

## 43. Actual candidate `htab_find_leaf_path` decomposition

`CandidateFindLeafShape.lean` peels the actual search function down to literal
subterms:

- four scopes `cap`, `path`, `node`, `depth`, then
  `seq candidateFindLeafLoop candidateFindLeafTail`;
- `candidateFindLeafLoop = while (node != 0) candidateFindLeafStep`;
- `candidateFindLeafStep = seq guard walk`, where `guard` is the
  `cap >= node` early-return branch and `walk = seq push (seq bump route)`;
- `candidateFindLeafPush` is exactly
  `store (path + depth*8) node`;
- `route = dec "route" (load node+16) (dec "b" ... (dec "m" ... child))`;
- `child` is the `b & m != 0` left/right child branch.

`candidateFindLeaf_body` and `candidateFindLeaf_body_scopes` are checked
against `sourceFunctionBody`; every other equation is `rfl`. Axioms are
`propext`, `Classical.choice`, `Quot.sound`.

This exposes the actual path-push statement and its address. Event/cost
composition with the `StatementRun.storeValue` rule and `PathMemoryInv.push`
is the next step; the binary-search/link tail of `htab_set` remains open.

## 44. Concrete path-push address

`PathMemoryInv.push_at` is the path-push invariant phrased for the candidate's
actual push address: an actual one-word store at an address equal to
`pathAddr base depth` advances the invariant to `depth+1`. This matches
`candidateFindLeafPush = store (path + depth*8) node` from section 43.

Axioms are `propext`, `Classical.choice`, `Quot.sound`.

## 45. Actual path-push `StatementRun` event/cost composition

`CandidateFindLeafPush.lean` proves, for the candidate statement
`push = store (path + depth*8) node`:

- `candidateFindLeafPush_run`: an actual `CostedExpressionRun` for the address
  expression and a `.val (.word node)` for the source produces the actual
  `StatementRun.storeValue` rule for `candidateFindLeafPush`, with events
  `.statement :: (addressEvents ++ valueEvents ++ [.memory 1, .cost (storeOverhead 1)])`;
- `candidateFindLeafPush_score`: the actual score of those events is
  `statements + addressEvents + valueEvents + memoryAccesses +
  nativeCost * storeOverhead 1`;
- `candidateFindLeafPush_preserves`: the same actual one-word store advances
  `PathMemoryInv` to `depth+1` at `pathAddr base depth`.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. This composes the actual
candidate push statement with the actual store rule and path invariant; the
surrounding loop/guard trace and the binary-search/link tail remain open.

## 46. Actual one-iteration search trace

`CandidateFindLeafStepTrace.lean` decomposes an actual successful
`StatementRun` of one `htab_find_leaf_path` iteration:

- `candidateFindLeafStep_run_split`: `step = seq guard walk` splits into the
  guard run and walk run;
- `candidateFindLeafWalk_run_split`: `walk = seq push (seq bump route)` splits
  into the actual path-push, depth-bump, and route/child runs;
- `candidateFindLeafStep_trace`: the full event order is
  `guardEvents ++ (pushEvents ++ (bumpEvents ++ routeEvents))` with all four
  actual subruns;
- `candidateFindLeafStep_trace_score`: the actual event score is the sum of
  the four subrun scores.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. The loop driver
(multiple iterations, guard early exit, endpoint tail) and the binary-search/
link/growth parts remain open.

## 47. Actual search-loop unfolding

`CandidateFindLeafLoopTrace.lean` proves that any actual successful
`StatementRun` of `candidateFindLeafLoop` is one of:

- stop: guard evaluated to `0`, events
  `.statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents`;
- continue iteration: a `whileNext` run with a `none`-result body step and a
  rest loop run, events `prefix ++ (guardEvents ++ bodyEvents ++ restEvents)`;
- break exit: a `whileBreak` run;
- continue exit: a `whileContinue` run.

All branches carry the actual guard/body/rest `StatementRun`s. Axioms are
`propext`, `Classical.choice`, `Quot.sound`.

This is the loop-driver unfolding step; recursively applying it to the rest
run yields the finite iteration list, after which the endpoint tail must be
composed.

## 48. Actual `htab_set` leaf-body structure

`CandidateHtabSetLeafShape.lean` pins the exact body passed to
`decCall "leaf" htab_find_leaf_path` and peels it into literal subterms:

- `candidateHtabSetLeaf_body`: duplicate-check prefix followed by the
  insertion tail;
- `candidateHtabSetLeaf_growth`: `cap < (count+1)*2` branch calling
  `htab_grow`, reloading `cap`, and re-running `htab_find_leaf_path` into
  `leaf`;
- `candidateHtabSetLeaf_bsearch`: the `while lo < hi` binary-search loop,
  including the double-load `mr = load ((load (path + mid*8)) + 16)`;
- `candidateHtabSetLeaf_sideStores`: `store nip cur` / `store (nip+8)
  new_leaf` and the mirrored side;
- `candidateHtabSetLeaf_link`: root `t+72` store or parent left/right store by
  `dir`;
- `candidateHtabSetLeaf_posSeq`: order array, order_pos, count update, return.

Axioms are `propext`, `Classical.choice`, `Quot.sound`. These are actual AST
equations, not an abstract model. Their `StatementRun`/cost composition is the
remaining step.

## 49. Actual side-link store traces

`CandidateHtabSetLinkTrace.lean` proves:

- `candidateHtabSetSideStores_trace`: an actual successful run of the
  side-store block is either the `side != 0` arm (`store nip cur; store
  (nip+8) new_leaf`) or the zero arm (`store nip new_leaf; store (nip+8)
  cur`), with the actual `ite` guard events and branch run;
- `candidateHtabSetSideStorePair_trace`: either two-store arm splits into the
  actual first and second `StatementRun`s.

Axioms are `propext`, `Classical.choice`, `Quot.sound`.

This covers the actual child-link writes at `nip`/`nip+8`; the root/parent
link block and bsearch/growth composition remain.

## 50. Actual root-or-parent link split

`candidateHtabSetLink_outer` splits an actual successful run of the link block
into the root store (`store (t+72) new_int`) or the `pp` scope containing the
`dir`-selected left/right parent store. Axioms are `propext`,
`Classical.choice`, `Quot.sound`.

## 51. Actual binary-search loop unfolding

`CandidateHtabSetBsearchTrace.lean` defines the literal one-iteration body
`candidateHtabSetBsearchStep` and proves any actual successful
`candidateHtabSetBsearch` run is one of: false-guard stop, `whileNext`
iteration, `whileBreak`, or `whileContinue`, with the actual event prefix
`.statement :: .cost (whileOverhead + loopMoves fn) :: ...` and the actual
guard/body/rest runs. Axioms are `propext`, `Classical.choice`, `Quot.sound`.

## 52. Actual binary-search iteration declarations

`CandidateHtabSetBsearchStepTrace.lean` splits one actual successful
binary-search iteration at its `mid` and `mr` declarations. Each split carries
the actual initializer events, the declaration frame event, and the actual
body run, with the declaration's local-environment post-state recorded
explicitly. Axioms are `propext`, `Classical.choice`, `Quot.sound`.

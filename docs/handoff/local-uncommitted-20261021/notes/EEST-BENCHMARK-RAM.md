# EEST v21.0.5 benchmark memory probe

On 2026-10-07, the existing `guest/build/guest.elf` was run under
`tools/spike/spike_run` against selected stateless cases from the
[`tests-zkevm-benchmark@v21.0.5` release](https://github.com/ethereum/execution-specs/releases/tag/tests-zkevm-benchmark%40v21.0.5).
The five assets contain 2,514, 2,518, 2,524, 2,528 and 2,528 guest invocations
for the 30M, 60M, 100M, 150M and 200M labels, respectively. The converter in
`tools/eest-stateless-to-input.py` emitted all 12,612 inputs into
`work/eest-benchmark-v21.0.5/`.

**Scope matters:** all of these fixtures set the execution payload's declared
`gasLimit` to 1,000,000,000,000, regardless of the benchmark label. The label
usually tracks the block header's *gas used*, and a few cases exceed their label
substantially. No fixture is therefore inside the challenge's declared-gas-limit
condition of at most 200M, even if its gas used is at most 200M. These runs probe
behavior and memory growth; they do not prove absence of source OOM under the
challenge's condition.

## Method

For each label, a script chose successful-output cases with header `gasUsed`
between half the label's gas value and the full label's value. At 30M and 200M,
it took the largest input in seven families: block-level access lists, account
queries, EVM memory, storage, logs, modexp and transaction types. At 60M, 100M
and 150M, it took the largest input in the access-list, memory and transaction
families. Five additional 200M memory cases exercise nested and sibling frames,
`MCOPY`, memory access and `MSIZE` with a 1 MiB setting. These are targeted
samples, not a full release pass or a random draw.

`tools/eest-run.py --measure-rss` measured each Spike process with GNU `time`.
The sample batches used three or four workers and 900- or 1,200-second per-case
timeouts. The two 200M retries each used one worker, a 500-billion instruction
cap, and a 1,800-second timeout. For example, to replay the selected 200M
cases from this checkout:

```sh
SPIKE_STEP_CAP=500000000000 python3 tools/eest-run.py \
  guest/build/guest.elf work/eest-benchmark-v21.0.5/0200M/inputs/manifest.tsv \
  --labels work/eest-benchmark-v21.0.5/0200M/sample-labels.txt \
  --jobs 4 --measure-rss --case-timeout 1800 \
  --out-dir work/eest-benchmark-v21.0.5/0200M/replay-run \
  --json work/eest-benchmark-v21.0.5/0200M/replay-results.json
```

The metric is peak **host resident set size** (RSS), including Spike itself and
the pages it touched in the simulated memory. The guest's configured 29 GiB RAM
is a virtual address range; RSS does not measure the highest address allocated
by the Pancake bump allocator and is not a bound on source memory use.
All fixture comparisons use the existing root/success/tail check. The tested
ELF is SHA-256 `930915c737fe769e0c967faea8cbfa1755ad1f949f544c726cf1ab8acc920b4f`.

## Passing scaling examples

Peak Spike RSS, in MiB, for three matched workload families:

| Workload | 30M | 60M | 100M | 150M | 200M |
| --- | ---: | ---: | ---: | ---: | ---: |
| Prefetch cold storage | 53.7 | 95.1 | 146.9 | 236.5 | 288.0 |
| `MSIZE`, zero memory size | 15.6 | 21.1 | 26.9 | 35.2 | 43.7 |
| Ether transfers | 80.8 | 151.8 | 249.1 | 373.6 | 484.4 |

All fifteen cases in this table halted cleanly and matched the EEST expected
result. A direct final-state dump of the guest heap pointer on the same ELF gave
52.4 MiB allocated above `HEAP_BASE` for 30M prefetch, 249.3 MiB for 200M
prefetch, and 457.9 MiB for 200M transfers. These are **final** pointer values,
not peak heap usage; the guest can release its bump pointer during execution.
The dump reads the compiled artifact's last scalar global at `0x7defffff8`,
which must be rechecked if the ELF changes.

All five additional 200M memory cases also matched: nested frames (11.2 MiB
peak RSS), sibling frames (16.2 MiB), `MCOPY` (11.7 MiB), memory access
(11.7 MiB), and `MSIZE` with a 1 MiB setting (12.6 MiB). Their execution took
between 1.4 billion and 38.1 billion Spike instructions.

The final per-case sample results are in
`work/eest-benchmark-v21.0.5/final-sample-results.json`, with individual logs
under the same work directory. A 30M storage case reached the runner's default
20-billion-instruction cap, then passed with a 200-billion cap at 23.7 billion
instructions and 38.4 MiB peak RSS. `SPIKE_STEP_CAP` now permits a higher limit
for benchmark runs while leaving the default unchanged. The result of a cap or
wall-clock timeout is **unfinished**, not a guest failure or OOM.
The selected 200M account-query case reached the 200-billion cap, then passed
with a 500-billion cap at 297.1 billion instructions and 273.3 MiB peak RSS.
The selected 200M cold-storage case likewise passed on retry at 459.3 billion
instructions and 182.3 MiB peak RSS. Thus all **28 distinct benchmark samples**
passed; none produced a guest OOM trap. This does not imply that the other
12,584 benchmark invocations pass.

The measured cases cannot establish a worst-case no-OOM claim. That requires an
allocation bound over all valid inputs with declared gas limit at most 200M,
including adversarial transactions and witness/input sizes. The older
[allocation audit](ALLOC-AUDIT.md) describes a superseded 240 MiB layout; the
current heap spans nearly 29 GiB as specified in [the challenge](CHALLENGE.md#memory-layout).

## In-scope cross-check from the standard EEST release

The benchmark fixtures' 1-trillion declared gas limit makes them unsuitable
for a direct challenge-condition test. As a separate cross-check, the same ELF
was rerun against thirteen `tests-zkevm@v21.0.1` cases whose declared gas
limit is at most 200M: all eight successful-output cases declaring exactly
200M, and the five largest inputs among successful-output cases within the
limit. All thirteen matched their expected output. The exact-200M set peaked
at 13.7 MiB Spike RSS; the largest-input set peaked at 52.0 MiB. The largest
input was 541,063 bytes and declared 100M gas. These cases are still a small
sample and do not exercise worst-case allocation.

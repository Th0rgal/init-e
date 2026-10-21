# Candidate source-price harness (frontend-only)

No `.lake` builds. Uses the fleet shared olean path plus the prebuilt
`work/cost-source-build/lib/lean` pricing modules.

```sh
SHARED=$(cat /home/zksecurity/trim-space/init-e/work/finite-auth-work/shared_lean_path.txt)
LEAN=/home/zksecurity/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean
$LEAN -o .build/CandidateAst.olean CandidateAst.lean
LEAN_PATH=".build:$SHARED:/home/zksecurity/trim-space/init-e/work/cost-source-build/lib/lean" \
  $LEAN --run HotspotPrice.lean
```

`CandidateAst.lean` is the generated Pancake AST for the frozen candidate
(`a97b7463...`), namespace `Candidate`. `HotspotPrice.lean` compiles it through
the frontend to Loop→Word and prices one executed loop body with
`preX = lineBound preAllocLeafBudget (instSelectExecutable riscvConfig 100000 e)`.

Observed preIsel source prices (diagnostic, not a checked bound):

| function | label | whole body | isolated loop body |
|---|---|---|---|
| htab_find_leaf | 103 | 920 | 816 per internal visit |
| htab_find_leaf_path | 104 | 1256 | 1080 per internal visit |
| htab_set (binary search) | 109 | 1198 | 590 per search step |
| htab_grow | 108 | 3647 | 1464 per growth loop |
| htab_truncate | 111 | 882 | 874 per truncation step |

All-true/left-right decision probes give the same loop-body price because the
left/right branches are price-symmetric; the three consumed dynamic decisions
are the loop condition, the leaf check, and the child direction.

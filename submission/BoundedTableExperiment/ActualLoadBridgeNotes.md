# Bridge notes: `candidateFindLeafRoute` -> `NodeLinkInv` memory loads

Read-only analysis of:

- `submission/BoundedTableExperiment/CandidateFindLeafShape.lean`
- `submission/BoundedTableExperiment/CandidateFindLeafStepTrace.lean`
- `submission/BoundedTableExperiment/CandidateFindLeafLoopTrace.lean`
- `submission/BoundedTableExperiment/ActualLinkMemoryInvariant.lean`
- `submission/BoundedTableExperiment/ActualRouteDepthBound.lean`
- `submission/InitECandidate/Runtime/PanStatementWork.lean`
- `submission/InitECandidate/Runtime/PanTotalExpressionCost.lean`
- `submission/InitECandidate/Runtime/PanExpressionWork.lean`
- `submission/InitECandidate/Runtime/LoadOneRead.lean`
- `submission/InitECandidate/Runtime/TwoWordValueShape.lean`
- `submission/InitECandidate/Runtime/RlpPutBeMemoryWindow.lean` (local-write lookup helpers)
- `submission/InitECandidate/Runtime/RlpEncodeBytesPrefix.lean` (`lookup_resVarEq_ne`)
- Flapjack: `PanSem/EvalExact.lean`, `PanSem/MemLoadHOL.lean`, `WordLang.lean`,
  `Compiler/Encoders/Asm.lean`.

No repo files were modified. Scratch Lean checks were done in `/tmp`.

---

## 1. The relevant syntax

From `CandidateFindLeafShape.lean`:

```lean
def localAddr (name : MlS) (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .local name,.const offset]

def candidateFindLeafChild : ProgHOL 64 :=
  .ite (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
      (.const (0 : BitVec 64)))
    (.assign .local (ofString "node") (.load .one (localAddr (ofString "node") 8)))
    (.assign .local (ofString "node") (.load .one (.var .local (ofString "node"))))

def candidateFindLeafMask : ProgHOL 64 :=
  .dec (ofString "m") .one (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)])
    candidateFindLeafChild

def candidateFindLeafByte : ProgHOL 64 :=
  .dec (ofString "b") .one
    (.loadByte (.op .add [.var .local (ofString "key"),
      .shift .asr (.var .local (ofString "route")) (.const (BitVec.ofNat 64 8))]))
    candidateFindLeafMask

def candidateFindLeafRoute : ProgHOL 64 :=
  .dec (ofString "route") .one (.load .one (localAddr (ofString "node") 16))
    candidateFindLeafByte
```

`NodeLinkInv` (`ActualLinkMemoryInvariant.lean`):

```lean
structure NodeLinkInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node : BitVec 64) (left right route : BitVec 64) : Prop where
  leftAt : s.memory node = .word left
  rightAt : s.memory (node + 8) = .word right
  routeAt : s.memory (node + 16) = .word route
```

**Naming convention is critical.** `NodeLinkInv.left` is the word at `node`;
`NodeLinkInv.right` is the word at `node + 8`. The candidate's `ite` condition
`(b &&& m) != 0` takes the **`node + 8`** arm and the zero arm takes **`node`**:

| condition | candidate branch | address | `NodeLinkInv` word |
|---|---|---|---|
| `byte &&& mask ≠ 0` | `.assign node (.load .one (localAddr node 8))` | `node + 8` | `right` |
| `byte &&& mask = 0` | `.assign node (.load .one (.var .local node))` | `node` | `left` |

So the final local is

```lean
if byte &&& mask = 0 then left else right
```

not the other way round.

---

## 2. Constructors and rules that matter

### `StatementRun` (`PanStatementWork.lean`, `InitECandidate.Runtime.FineCost`)

`StatementRun` is an indexed inductive with constructor names:

- sequence: `.seqNext`, `.seqStop`.
- `.ite`: `.iteYes`, `.iteNo`, plus `.iteInvalidGuard`.
- `.dec`: `.declareValue` (the only successful, `result = none` case), plus
  `.declareMismatch` / `.declareFailure` (both produce `some .error` and are
  therefore impossible in a `none post` run).
- `.assign`: `.assignValue` (successful), `.assignInvalid`, `.assignFailure`.
- `.store` / `.storeByte` / `.store32`: `.storeValue` etc.
- `.while`: `.whileFalse`, `.whileNext`, `.whileContinue`, `.whileBreak`,
  `.whileTimeout`, `.whileMissingGuard`, `.whilePropagate`.
- `.tick`: `.tickStep`, `.tickTimeout`; `.skip`, `.annotation`; `.return...`;
  `.call...` / `.decCall...`; `.primitive...`; `.raise...`; `.external`,
  `.sharedLoad`, `.sharedStore`.

The three rules used by this bridge have exactly these fields:

```lean
| declareValue {fn} {s name shape initializer body value initEvents bodyEvents result post}
    (init : CostedExpressionRun s initializer (some value) initEvents)
    (shapeMatch : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (bodyRun : StatementRun fn (setVarHOLFinite name value s) body result post bodyEvents) :
    StatementRun fn s (.dec name shape initializer body) result
      { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
      (.statement :: (initEvents ++ [.frame 1] ++ bodyEvents))

| iteYes {fn} {s condition yes no value guardEvents r post bodyEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : value ≠ 0)
    (body : StatementRun fn s yes r post bodyEvents) :
    StatementRun fn s (.ite condition yes no) r post
      (.statement :: .cost (statementUnit + branchMoves fn) :: (guardEvents ++ bodyEvents))

| iteNo {fn} {s condition yes no guardEvents r post bodyEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents)
    (body : StatementRun fn s no r post bodyEvents) :
    StatementRun fn s (.ite condition yes no) r post
      (.statement :: .cost (statementUnit + branchMoves fn) :: (guardEvents ++ bodyEvents))

| assignValue {fn} {s kind name expression value events}
    (expr : CostedExpressionRun s expression (some value) events)
    (valid : isValidValueHOLFinite s kind name value = true) :
    StatementRun fn s (.assign kind name expression) none
      (setKvarHOLFinite kind name value s)
      (.statement :: (events ++ .copy (flattenHOL value).length ::
        globalEvents kind (flattenHOL value).length))
```

The resulting event shapes for `.dec`, `.ite`, and `.assign` are therefore
`initEvents ++ [.frame 1] ++ bodyEvents`,
`.statement :: .cost (...) :: (guardEvents ++ branchEvents)`, and
`.statement :: (events ++ .copy 1 :: globalEvents .local 1)` respectively.

`StatementRun.sound` exists (`theorem StatementRun.sound : StatementRun fn s p r post
events -> evaluateHOLFiniteState s p = (r, post)`), but it is **not sufficient**
for this bridge: it only gives the final evaluator pair and does not expose
which `ite` arm or which internal load fired. Use `cases` on the constructor
instead.

### `CostedExpressionRun` (`PanTotalExpressionCost.lean`)

There is **no per-expression constructor**, in particular no `.load`
constructor. It is a structure:

```lean
structure CostedExpressionRun {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (value : Option (ValueHOL 64)) (events : List WorkEvent) : Prop where
  sound : expressionValue s e = value
  events_eq : events = expressionEvents s e
```

with total constructor

```lean
theorem costedExpressionRun_total (s) (e) :
    CostedExpressionRun s e (expressionValue s e) (expressionEvents s e) := ⟨rfl, rfl⟩
```

So `init.sound` is the bridge from a successful `.dec`/`.assign` expression to
the actual evaluator. `expressionValue` is a `noncomputable def` in
`InitECandidate.Runtime.FineCost`:

```lean
noncomputable def expressionValue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
```

so `unfold expressionValue at init.sound` turns it into the exact
`@evalHOLExact ...` equation used by the runtime lemmas.

### Raw `.load` semantics (`EvalExact.lean`, `MemLoadHOL.lean`)

`evalHOLExact` for `.load shape address`:

```lean
| .load shape address =>
    if isWfShapeExactHOL state.structs shape then
      match evalHOLExact state address with
      | some (.val (.word word)) =>
          memLoadHOLExact shape word state.memaddrs state.memory state.structs
      | _ => none
    else none
```

and for `.one` (`MemLoadHOL.lean`):

```lean
| .one => if domain address then some (.val (memory address)) else none
```

The existing runtime lemma that exposes domain and word is
`InitECandidate.Runtime.eval_load_one_read` (`LoadOneRead.lean`):

```lean
theorem eval_load_one_read {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.load .one address) = some value) :
    ∃ pointer word : BitVec 64,
      @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) address = some (.val (.word pointer)) ∧
      state.memaddrs pointer ∧ state.memory pointer = .word word ∧
      value = .val (.word word)
```

This is the main memory-read bridge. It returns the pointer, domain
membership, memory cell, and the loaded word.

Existing related helpers:

- `InitECandidate.Runtime.actual_payload_header_eval_load_word` proves
  `evalHOLExact (.load .one (.op .add [.var .local name, .const offset])) = some (.val (.word value))`
  **given `memaddrs (base + offset)` and `memory (base + offset) = .word value`.**
  It cannot be used to derive the pointer or the domain, because it requires
  them as hypotheses.
- `InitECandidate.Runtime.eval_load_one_val` only gives `∃ cell, value = .val cell`.
- `InitECandidate.Runtime.eval_binop_returns_word` / `eval_shift_returns_word`
  only prove the result is a word, not its value.
- `InitECandidate.Runtime.value_word_of_shape_one`:
  `shapeOfHOLExact value = .one -> ∃ word, value = .val (.word word)`.

### Word operation facts (needed for mask / guard)

`wordOpHOL` is `Flapjack.wordOp` (`WordLang.lean`):

```lean
| .and, values => some (values.foldr (fun l r => AndOp.and l r) (Complement.complement (0 : α)))
| .add, values => some (values.foldr (fun l r => l + r) 0)
| .or,  values => some (values.foldr (fun l r => OrOp.or l r) 0)
| .xor, values => some (values.foldr (fun l r => HXor.hXor l r) 0)
```

(Checked with `#eval`: `wordOp .xor [1, 255] = some 254`, i.e. the seed for
`.xor` is `0`, not `complement 0`. `wordOp .and [1, 255] = some 1`.)

Consequences:

```lean
-- b is a BitVec 64, m likewise
wordOp .and [b, m] = some (b &&& (m &&& ~~~(0 : BitVec 64))) = some (b &&& m)
wordOp .xor [route, 255] = some (route ^^^ (255 ^^^ 0)) = some (route ^^^ 255)
```

`wordCmpHOL` (`Compiler/Encoders/Asm.lean`):

```lean
| .notEqual => !(left == right)
```

and `evalHOLExact` turns the `Bool` into `1`/`0`:

```lean
some (.val (.word (if wordCmpHOL .notEqual left right then 1 else 0)))
```

Hence the guard `(.cmp .notEqual (.op .and [b,m]) (.const 0))` evaluates to

```lean
some (.val (.word (if b &&& m = 0 then 0 else 1)))
```

---

## 3. Proposed exact theorem statements

All in `namespace BoundedTableExperiment`, with the existing opens:

```lean
open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
```

Use `MlS` and `ofString`; in the code below the names are written out to avoid
notation ambiguity.

### 3.1 Missing evaluation helpers (put these first)

```lean
/-- Evaluate a local + constant address. -/
theorem eval_localAddr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (base offset : BitVec 64)
    (localLookup : s.locals.lookup name = some (.val (.word base))) :
    expressionValue s (localAddr name offset) =
      some (.val (.word (base + offset))) := by
  -- Compiles as-is (checked in /tmp): the .add fold leaves base + (offset + 0),
  -- and simp closes BitVec.add_zero.
  simp [localAddr, expressionValue, evalHOLExact, evalListHOLExact, localLookup,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- Evaluate a bare local used as a load address (the zero arm). -/
theorem eval_localWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (word : BitVec 64)
    (localLookup : s.locals.lookup name = some (.val (.word word))) :
    expressionValue s (.var .local name) = some (.val (.word word)) := by
  simpa [expressionValue, evalHOLExact] using localLookup

/-- The mask declaration expression: `wordOp .xor` seed is 0, so this is
`route ^^^ 255`, not `~~~(route ^^^ 255)` and not `route ^^^ ~~~255`. -/
theorem eval_candidateFindLeafMask {F : Type} (s : PanSemStateFiniteExact 64 F)
    (route : BitVec 64)
    (routeLocal : s.locals.lookup (ofString "route") = some (.val (.word route))) :
    expressionValue s
      (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)]) =
      some (.val (.word (route ^^^ BitVec.ofNat 64 255))) := by
  -- Compiles as-is (checked in /tmp).
  simp [expressionValue, evalHOLExact, evalListHOLExact, routeLocal,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- The `(b &&& m) != 0` guard. -/
theorem eval_candidateFindLeafChildGuard {F : Type}
    (s : PanSemStateFiniteExact 64 F) (b m : BitVec 64)
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m))) :
    expressionValue s
      (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
        (.const (0 : BitVec 64))) =
      some (.val (.word (if b &&& m = 0 then 0 else 1))) := by
  -- The AndOp fold leaves the `complement 0` seed; normalize it first.
  -- (Both lines below were compile-checked in /tmp.)
  have hand : AndOp.and b (AndOp.and m (18446744073709551615#64)) = b &&& m := by
    change b &&& (m &&& 18446744073709551615#64) = b &&& m
    bv_decide
  simp [expressionValue, evalHOLExact, evalListHOLExact, bLocal, mLocal,
    wordOpHOL, wordOp, valueIsWord, valueWord, hand,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
```

The `eval_localAddr`, `eval_localWord` and `eval_mask` proofs above compile
as-is. The guard proof needs the `hand` fact shown above because `wordOp .and`
leaves the `complement 0` seed (`AndOp.and m 18446744073709551615#64`) and
`bv_decide` cannot abstract `AndOp.and` directly; the `change` to `&&&` is
required. The exact `wordOp` source is above; do not guess the `.xor` seed.

The existing local-lookup helpers can be reused if the bridge file imports
`InitECandidate.Runtime.RlpPutBeMemoryWindow` and
`InitECandidate.Runtime.RlpEncodeBytesPrefix`:

```lean
theorem lookup_setVar_eq (s) (name) (v) :
  (setVarHOLFinite name v s).locals.lookup name = some v

theorem lookup_setVar_ne (s) (name other) (v x) (ne : name ≠ other)
    (h : s.locals.lookup other = some x) :
  (setVarHOLFinite name v s).locals.lookup other = some x

theorem lookup_resVarEq_ne (map : HolFiniteMapExact MlS (ValueHOL 64))
    (key name : MlS) (e : Option (ValueHOL 64)) (h : name ≠ key) :
  (HolFiniteMapExact.resVarEq map (key,e)).lookup name = map.lookup name
```

Otherwise prove local copies (they are three-line `simp` proofs; the
`resVarEq` one is in `RlpEncodeBytesPrefix.lean:95`).

### 3.2 T1: the exact `.dec` split of `candidateFindLeafRoute`

This mirrors `candidateHtabSetBsearchStep_mid` in
`CandidateHtabSetBsearchStepTrace.lean`.

```lean
theorem candidateFindLeafRoute_dec_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafRoute none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some value) initEvents ∧
      post = { bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals
        (ofString "route", s.locals.lookup (ofString "route")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "route") value s)
        candidateFindLeafByte none bodyPost bodyEvents := by
  rw [candidateFindLeaf_route] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩
```

Goal shape after `cases run` is exactly:

```lean
∃ value initEvents bodyEvents bodyPost,
  events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
  CostedExpressionRun s (.load .one (localAddr ...)) (some value) initEvents ∧
  post = {bodyPost with locals := resVarEq bodyPost.locals (routeName, ...)} ∧
  StatementRun fn (setVarHOLFinite routeName value s) candidateFindLeafByte none bodyPost bodyEvents
```

No `NodeLinkInv` is needed for T1.

### 3.3 T2: `route` is the word at `node + 16`

This is the bridge from the successful `route` declaration to
`NodeLinkInv.routeAt`.

```lean
theorem candidateFindLeafRoute_route {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route : BitVec 64}
    (run : StatementRun fn s candidateFindLeafRoute none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    ∃ (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some (.val (.word route))) initEvents ∧
      post = { bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals
        (ofString "route", s.locals.lookup (ofString "route")) } ∧
      StatementRun fn
        (setVarHOLFinite (ofString "route") (.val (.word route)) s)
        candidateFindLeafByte none bodyPost bodyEvents ∧
      s.memaddrs (node + 16) ∧
      (setVarHOLFinite (ofString "route") (.val (.word route)) s).locals.lookup
        (ofString "route") = some (.val (.word route))
```

Proof sketch:

```lean
obtain ⟨value, initEvents, bodyEvents, bodyPost, eventsEq, init, postEq, bodyRun⟩ :=
  candidateFindLeafRoute_dec_split run

have loaded := init.sound
unfold expressionValue at loaded
obtain ⟨pointer, word, addrEval, dom, cell, valueEq⟩ :=
  eval_load_one_read s (localAddr (ofString "node") 16) value loaded

have addrWord := eval_localAddr s (ofString "node") node 16 nodeLocal
have addrEval' :
    @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (localAddr (ofString "node") 16) = some (.val (.word (node + 16))) := by
  simpa [expressionValue] using addrWord

have pointerEq : pointer = node + 16 :=
  HolWordLab.word.inj
    (ValueHOL.val.inj (Option.some.inj (addrEval.symm.trans addrEval')))

have wordEq : word = route := by
  rw [pointerEq, inv.routeAt] at cell
  exact (HolWordLab.word.inj cell).symm

have valueEq' : value = .val (.word route) := by
  simpa [wordEq] using valueEq

refine ⟨initEvents, bodyEvents, bodyPost, eventsEq, ?_, postEq, ?_,
  ?_, ?_⟩
· simpa [valueEq'] using init
· simpa [valueEq'] using bodyRun
· simpa [pointerEq] using dom
· exact lookup_setVar_eq s (ofString "route") (.val (.word route))
```

Notes:

- `eval_load_one_read` gives `dom : s.memaddrs pointer`; after `pointerEq` this
  is `s.memaddrs (node + 16)`.
- `inv.routeAt` supplies `.word route`, so `word = route` by `HolWordLab.word.inj`.
- The route-local read is exactly `lookup_setVar_eq`; no `resVarEq` is involved
  yet because this is the body state inside the route `.dec`.
- The `NodeLinkInv` is only used for `routeAt`; if only the dec-load part is
  wanted, T2 is the theorem to prove.

### 3.4 T3: the child choice is a `NodeLinkInv` load

This is the generic leaf of the bridge. State it over an arbitrary state whose
`b`/`m`/`node` locals are known, so it can be reused inside the loop.

```lean
theorem candidateFindLeafChild_links {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route b m : BitVec 64}
    (run : StatementRun fn s candidateFindLeafChild none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m))) :
    ∃ (flag : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual
          (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
          (.const (0 : BitVec 64)))
        (some (.val (.word flag))) guardEvents ∧
      flag = if b &&& m = 0 then 0 else 1 ∧
      post.locals.lookup (ofString "node") =
        some (.val (.word (if b &&& m = 0 then left else right))) ∧
      post.memory = s.memory ∧
      (b &&& m ≠ 0 → s.memaddrs (node + 8)) ∧
      (b &&& m = 0 → s.memaddrs node)
```

Proof sketch:

```lean
rw [candidateFindLeaf_child] at run
cases run with
| iteYes guard nonzero body =>
    -- guard.sound + eval_candidateFindLeafChildGuard:
    --   guard value = if b &&& m = 0 then 0 else 1
    -- nonzero therefore gives hb : b &&& m ≠ 0
    -- body is the node+8 load assignment
    cases body with
    | assignValue expr valid =>
        -- expr.sound : expressionValue s (.load .one (localAddr node 8)) = some v
        -- unfold expressionValue; eval_load_one_read gives pointer/word/dom/cell/value
        -- eval_localAddr s nodeName node 8 nodeLocal gives pointer = node + 8
        -- inv.rightAt gives s.memory (node + 8) = .word right, hence word = right
        -- post is setKvarHOLFinite .local nodeName (.val (.word right)) s
        -- lookup_setVar_eq gives post.locals node = some (.val (.word right))
        -- final if is `if_neg hb`
        exact ⟨flag, guardEvents, branchEvents, rfl, guard, flagEq, ?_, rfl, ?_, ?_⟩
| iteNo guard body =>
    -- guard has literal value 0, so guard.sound + guard helper gives hz : b &&& m = 0
    -- body is the node load assignment
    cases body with
    | assignValue expr valid =>
        -- eval_localWord for (.var .local node), inv.leftAt -> word = left
        -- post.locals node = some (.val (.word left))
        exact ⟨flag, guardEvents, branchEvents, rfl, guard, flagEq, ?_, rfl, ?_, ?_⟩
```

Important proof details:

1. `iteYes` and `iteNo` **share the same event shape**, so the existential's
   first component is identical in both arms.
2. In the yes arm, the address is `localAddr nodeName 8`; use `eval_localAddr`.
   In the no arm, the address is `.var .local nodeName`; use `eval_localWord`
   (there is no `localAddr node 0` in the candidate).
3. `assignValue`'s post is `setKvarHOLFinite .local nodeName value s`, which
   unfolds to `setVarHOLFinite nodeName value s`; `lookup_setVar_eq` closes the
   node-local goal.
4. The two domain implications are exactly what `eval_load_one_read`'s `dom`
   component gives after rewriting the pointer. `post.memory = s.memory` is
   `rfl` for `assignValue` (assignment touches only locals).
5. Do not try to derive the loaded word from `inv.leftAt`/`rightAt` without
   first establishing the pointer equality from the address expression; the
   memory cell alone does not identify which address was read.

### 3.5 T4: full `candidateFindLeafRoute` corollary

This is the theorem to expose to the enclosing proof. It composes T2, the byte
and mask `.dec` splits, and T3.

```lean
theorem candidateFindLeafRoute_child_links {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route : BitVec 64}
    (run : StatementRun fn s candidateFindLeafRoute none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    ∃ (byte mask : BitVec 64),
      mask = route ^^^ BitVec.ofNat 64 255 ∧
      post.locals.lookup (ofString "node") =
        some (.val (.word (if byte &&& mask = 0 then left else right))) ∧
      post.memory = s.memory ∧
      post.memaddrs = s.memaddrs ∧
      s.memaddrs (node + 16) ∧
      (byte &&& mask ≠ 0 → s.memaddrs (node + 8)) ∧
      (byte &&& mask = 0 → s.memaddrs node)
```

If the caller needs the intermediate event decomposition, either use the
split theorems directly, or add the following conjuncts to T4:

```lean
∃ (routeEvents byteEvents maskEvents childEvents : List WorkEvent)
  (bodyPostR bodyPostB bodyPostM : PanSemStateFiniteExact 64 F),
  events = .statement :: (routeEvents ++ [.frame 1] ++
    (.statement :: (byteEvents ++ [.frame 1] ++
      (.statement :: (maskEvents ++ [.frame 1] ++ childEvents))))) ∧
  CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
    (some (.val (.word route))) routeEvents ∧
  CostedExpressionRun
    (setVarHOLFinite (ofString "route") (.val (.word route)) s)
    (.loadByte (.op .add [.var .local (ofString "key"),
      .shift .asr (.var .local (ofString "route")) (.const (BitVec.ofNat 64 8))]))
    (some (.val (.word byte))) byteEvents ∧
  CostedExpressionRun
    (setVarHOLFinite (ofString "b") (.val (.word byte))
      (setVarHOLFinite (ofString "route") (.val (.word route)) s))
    (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)])
    (some (.val (.word mask))) maskEvents ∧
  mask = route ^^^ BitVec.ofNat 64 255 ∧
  StatementRun fn
    (setVarHOLFinite (ofString "m") (.val (.word mask))
      (setVarHOLFinite (ofString "b") (.val (.word byte))
        (setVarHOLFinite (ofString "route") (.val (.word route)) s)))
    candidateFindLeafChild none bodyPostM childEvents
```

(Order of the three `.frame 1` wrappers is route, then byte, then mask.)

Proof sketch for T4:

```lean
-- 1. Route read.
obtain ⟨routeEvents, bodyEventsR, bodyPostR, eventsR, routeInit,
  postEqR, byteRun⟩ := candidateFindLeafRoute_route run inv nodeLocal

-- 2. Byte `.dec` at s1 = setVarHOLFinite route (word route) s.
--    Same `cases run with | declareValue init shapeMatch bodyRun =>` pattern.
--    value_word_of_shape_one turns the declared value into `.val (.word byte)`.
obtain ⟨byte, byteEvents, bodyEventsB, bodyPostB, eventsB, byteInit,
  postEqB, maskRun⟩ := candidateFindLeafByte_dec_split byteRun

-- 3. Route local in s1, then preserved through the b assignment:
have routeLocal1 : (setVarHOLFinite routeName (.val (.word route)) s).locals.lookup
    routeName = some (.val (.word route)) :=
  lookup_setVar_eq _ _ _
have routeLocal2 : (setVarHOLFinite bName (.val (.word byte))
    (setVarHOLFinite routeName (.val (.word route)) s)).locals.lookup routeName =
    some (.val (.word route)) :=
  lookup_setVar_ne _ bName routeName _ _ (by decide) routeLocal1

-- 4. Mask `.dec`; eval_candidateFindLeafMask + init.sound gives
--    mask = route ^^^ 255.
obtain ⟨mask, maskEvents, bodyEventsM, bodyPostM, eventsM, maskInit,
  maskEq, childRun⟩ := candidateFindLeafMask_dec_split maskRun routeLocal2

-- 5. b/m/node locals in s3 = setVarHOLFinite m (word mask) s2:
have bLocal3 : s3.locals.lookup bName = some (.val (.word byte)) :=
  lookup_setVar_ne _ mName bName _ _ (by decide) (lookup_setVar_eq _ _ _)
have mLocal3 : s3.locals.lookup mName = some (.val (.word mask)) :=
  lookup_setVar_eq _ _ _
have nodeLocal3 : s3.locals.lookup nodeName = some (.val (.word node)) :=
  -- route then b then m, each via lookup_setVar_ne and `by decide`
  ...
have inv3 : NodeLinkInv s3 node left right route := by
  simpa [NodeLinkInv] using inv

-- 6. Child choice.
obtain ⟨flag, guardEvents, branchEvents, childEventsEq, guardRun,
  flagEq, childNode, childMem, rightDom, leftDom⟩ :=
  candidateFindLeafChild_links childRun inv3 nodeLocal3 bLocal3 mLocal3

-- 7. Strip the three outer `resVarEq` restores. Each is a different key:
--    m, b, route; `node` is not any of them.
have nodeAfterR := lookup_resVarEq_ne _ routeName nodeName _ (by decide)
have nodeAfterB := lookup_resVarEq_ne _ bName nodeName _ (by decide)
have nodeAfterM := lookup_resVarEq_ne _ mName nodeName _ (by decide)
-- rewrite postEqR/postEqB/postEqM and the three lemmas, then
-- exact childNode (with `if` orientation already matching).

-- 8. Memory/memaddrs are untouched by all three decs and the assignment.
--    `simp [postEqR, postEqB, postEqM, childMem]` and similarly for memaddrs.

-- 9. Domains: rightDom/leftDom are in s3; `s3.memaddrs = s.memaddrs`
--    definitionally (setVar only changes locals).
```

Required byte/mask split statements (both follow the T1 pattern):

```lean
theorem candidateFindLeafByte_dec_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafByte none post events) :
    ∃ (byte : BitVec 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s
        (.loadByte (.op .add [.var .local (ofString "key"),
          .shift .asr (.var .local (ofString "route")) (.const (BitVec.ofNat 64 8))]))
        (some (.val (.word byte))) initEvents ∧
      post = { bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals
        (ofString "b", s.locals.lookup (ofString "b")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "b") (.val (.word byte)) s)
        candidateFindLeafMask none bodyPost bodyEvents := by
  rw [show candidateFindLeafByte = .dec (ofString "b") .one
    (.loadByte (.op .add [.var .local (ofString "key"),
      .shift .asr (.var .local (ofString "route")) (.const (BitVec.ofNat 64 8))]))
    candidateFindLeafMask from rfl] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      have hshape : shapeOfHOLExact _ = .one :=
        ((shapeEqHOL_eq_true _ _).mp shapeMatch).symm
      obtain ⟨byte, rfl⟩ := value_word_of_shape_one _ hshape
      exact ⟨byte, _, _, _, rfl, init, rfl, bodyRun⟩

theorem candidateFindLeafMask_dec_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafMask none post events)
    (route : BitVec 64)
    (routeLocal : s.locals.lookup (ofString "route") = some (.val (.word route))) :
    ∃ (mask : BitVec 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s
        (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)])
        (some (.val (.word mask))) initEvents ∧
      mask = route ^^^ BitVec.ofNat 64 255 ∧
      post = { bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals
        (ofString "m", s.locals.lookup (ofString "m")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "m") (.val (.word mask)) s)
        candidateFindLeafChild none bodyPost bodyEvents := by
  rw [show candidateFindLeafMask = .dec (ofString "m") .one
    (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)])
    candidateFindLeafChild from rfl] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      have hshape : shapeOfHOLExact _ = .one :=
        ((shapeEqHOL_eq_true _ _).mp shapeMatch).symm
      obtain ⟨mask, rfl⟩ := value_word_of_shape_one _ hshape
      have maskEval := eval_candidateFindLeafMask s route routeLocal
      have maskEq : mask = route ^^^ BitVec.ofNat 64 255 := by
        have eq := init.sound.symm.trans maskEval
        exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj eq))
      exact ⟨mask, _, _, _, rfl, init, maskEq, rfl, bodyRun⟩
```

(If the value's shape is already a word by construction, the
`value_word_of_shape_one` step may of course be replaced by a direct case split;
`loadByte` always yields `.val (.word _)`, but the `.dec` shape check is the
reusable uniform route.)

---

## 4. What is missing in the repo

Genuinely missing (no existing declaration found):

1. **`eval_localAddr` / `eval_localWord`** — evaluation of the candidate's
   address expressions from locals alone. Needed to prove the pointer returned
   by `eval_load_one_read` equals `node + 16` / `node + 8` / `node`. The
   existing `actual_payload_header_eval_load_word` cannot bootstrap the
   `memaddrs` hypothesis, so it is not a substitute.
2. **`eval_candidateFindLeafMask`** — evaluation of `.op .xor [route, 255]`.
   Needed for `mask = route ^^^ 255`.
3. **`eval_candidateFindLeafChildGuard`** — evaluation of the `(b &&& m) != 0`
   comparison to `if b &&& m = 0 then 0 else 1`. Needed to invert the `iteYes`
   `nonzero` and identify the `iteNo` zero arm.
4. **Struct split lemmas for the three `.dec`s and the child `.ite`**
   (`candidateFindLeafRoute_dec_split`, `candidateFindLeafByte_dec_split`,
   `candidateFindLeafMask_dec_split`, `candidateFindLeafChild_links`). The
   existing `CandidateFindLeafStepTrace` only splits `seq`/`while` and reaches
   `candidateFindLeafRoute` as a whole; it does not open its `.dec` or `.ite`.
5. **`resVarEq` other-key lookup** already exists as
   `InitECandidate.Runtime.lookup_resVarEq_ne` in
   `RlpEncodeBytesPrefix.lean:95`, and `lookup_setVar_eq`/`lookup_setVar_ne`
   exist in `RlpPutBeMemoryWindow.lean:36,44`, but the bridge file must import
   those (heavy RLP modules) or copy the three-line proofs.
6. **No `loadByte` read bridge** is needed for the *link* result: the child
   choice only needs the byte value as a bitmap, not its address or memory
   cell. If a later proof needs the actual byte source, it is a separate
   missing lemma (there is `eval_load_one_read` for `.load`, but no analogue
   for `.loadByte`).

Existing pieces to reuse:

- `InitECandidate.Runtime.eval_load_one_read` (`LoadOneRead.lean`).
- `InitECandidate.Runtime.value_word_of_shape_one` (`TwoWordValueShape.lean`).
- `Flapjack.shapeEqHOL_eq_true` (`IsValidValueExact.lean`).
- `InitECandidate.Runtime.lookup_setVar_eq` / `lookup_setVar_ne`
  (`RlpPutBeMemoryWindow.lean`).
- `InitECandidate.Runtime.lookup_resVarEq_ne` (`RlpEncodeBytesPrefix.lean`).
- `Flapjack.HolWordLab.word.inj`, `Flapjack.ValueHOL.val.inj`,
  `Option.some.inj` for the pointer/word injections.
- `CandidateFindLeafStepTrace.candidateFindLeafWalk_run_split` already gives
  the actual `StatementRun ... candidateFindLeafRoute` from a loop iteration;
  T2/T4 consume exactly that run.

Suggested new file: `submission/BoundedTableExperiment/CandidateFindLeafLinkTrace.lean`
with imports:

```lean
import CandidateFindLeafShape
import ActualLinkMemoryInvariant
import InitECandidate.Runtime.LoadOneRead
import InitECandidate.Runtime.TwoWordValueShape
-- only if reusing the RLP helpers:
import InitECandidate.Runtime.RlpPutBeMemoryWindow
import InitECandidate.Runtime.RlpEncodeBytesPrefix
```

---

## 5. Gotchas / checks

0. **Do not name a binder `local`.** `local` is a Lean parser keyword; the
   compiled scratch used `localLookup`. The statements below already use
   `localLookup` / `bLocal` / `mLocal`.
1. **`mask = route ^^^ 255`, not `route ^^^ ~~~255`.** I initially suspected
   the `wordOp` seed was `complement 0` (as in `evalLoopWordOp`'s `.and`), but
   `Flapjack.Pancake.WordLang.wordOp` uses seed `0` for `.xor`; `#eval` with
   real oleans gives `wordOp .xor [1, 255] = some 254`. Use the `wordOp`
   source/probe, not the neighbouring `evalLoopWordOp`.
2. **The candidate's `ite` is not the usual "left if bit set" convention.**
   Nonzero `(b &&& m)` loads `node + 8` (`NodeLinkInv.right`); zero loads
   `node` (`NodeLinkInv.left`).
3. **`NodeLinkInv` is about the original state `s`.** Every `.dec` only changes
   `locals`, and the child `assign` only changes `locals`, so
   `NodeLinkInv s node left right route` transports to the child-entry state
   by `simpa [NodeLinkInv] using inv`. There are no memory stores in this
   route, hence `post.memory = s.memory`.
4. **`post` after the route `.dec` restores `route`, not `node`.** The final
   `post.locals.lookup "node"` is the child assignment's value; the three
   `resVarEq` restores for `m`, `b`, `route` must be stripped using
   `lookup_resVarEq_ne` with `nodeName ≠ ...` (`by decide`).
5. **`StatementRun.sound` cannot replace `cases` here.** It collapses the
   whole program to `evaluateHOLFiniteState s candidateFindLeafRoute = (none, post)`
   and hides the `ite` arm and the internal loads. Use constructor induction +
   `CostedExpressionRun.sound`.
6. **`CostedExpressionRun` is a structure, not an inductive.** `init.sound` and
   `init.events_eq` are projections; there is no `CostedExpressionRun.load`.
   The `.load` semantics is reached by unfolding `expressionValue` to
   `evalHOLExact` and then `memLoadHOLExact`.
7. **`eval_load_one_read`'s value orientation is**
   `value = .val (.word word)` (the word is on the right). `init.sound` is
   `expressionValue ... = some value`; after unfolding, pass it directly.
8. **`localAddr` is reducibly `.op .add [.var .local name, .const offset]`.**
   If address arithmetic is done with `simp`, the `.add` fold leaves
   `base + (offset + 0)`; `BitVec.add_zero` or `simpa` is usually enough.
   `eval_localWord` is needed for the zero arm because the source uses
   `.var .local node`, not `.op .add [node, 0]`.

---

## 6. Exact goal shapes checklist

After `rw [candidateFindLeaf_route] at run; cases run with | declareValue ...`,
T1's goal is the six-part existential shown in §3.2. T2's route-load goal is:

```lean
CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
  (some (.val (.word route))) initEvents
```

and the memory goal after `eval_load_one_read` + `eval_localAddr` is:

```lean
pointer = node + 16
s.memaddrs (node + 16)
s.memory (node + 16) = .word route
```

T3's child goal splits exactly into:

```lean
-- iteYes:
value ≠ 0
StatementRun fn s (.assign .local (ofString "node")
  (.load .one (localAddr (ofString "node") 8))) none post branchEvents
-- iteNo:
StatementRun fn s (.assign .local (ofString "node")
  (.load .one (.var .local (ofString "node")))) none post branchEvents
```

after computing the guard. The final node-local goal is:

```lean
post.locals.lookup (ofString "node") =
  some (.val (.word (if byte &&& mask = 0 then left else right)))
```

with the three `resVarEq` restores already stripped.


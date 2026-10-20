import InitECandidate.Runtime.PanCostTotal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- Score of one statement-entry event: the statement coefficient only. -/
theorem score_statement_event (coeff : Work) :
    coeff.score (WorkEvent.statement).units = coeff.statements := by
  simp [Work.score, WorkEvent.units]

/-- Arithmetic core for one continuing iteration: the body pays `C` per consumed
unit plus a fixed prefix `B`, the loop statement entry and guard pay `D`, and the
remaining loop already fits `(C + B + D) * delta + (B + D)`. Consuming at least
one unit makes the fixed prefixes affordable per unit. -/
theorem gas_budget_continue_arith {start middle post C B D : Nat}
    (hmono : middle ≤ post) (hprogress : start + 1 ≤ middle) :
    C * (middle - start) + ((C + B + D) * (post - middle) + (B + D)) + D + B ≤
      (C + B + D) * (post - start) + (B + D) := by
  have delta : post - start = (middle - start) + (post - middle) := by omega
  have split : (C + B + D) * ((middle - start) + (post - middle)) =
      (C + B + D) * (middle - start) + (C + B + D) * (post - middle) := Nat.mul_add _ _ _
  have inner : (C + B + D) * (middle - start) =
      C * (middle - start) + (B + D) * (middle - start) := by
    rw [Nat.add_assoc, Nat.add_mul]
  have slack : B + D ≤ (B + D) * (middle - start) :=
    Nat.le_mul_of_pos_right (B + D) (by omega)
  rw [delta, split, inner]
  omega

/-- Arithmetic core for a terminal iteration (break or propagated result). No gas
progress is available on such a path, only the fixed terminal prefix. -/
theorem gas_budget_terminal_arith {start post C B D : Nat} (hmono : start ≤ post) :
    C * (post - start) + B + D ≤ (C + B + D) * (post - start) + (B + D) := by
  by_cases zero : post - start = 0
  · rw [zero]
    simp only [Nat.mul_zero]
    omega
  · have positive : 0 < post - start := by omega
    have slack : B + D ≤ (B + D) * (post - start) :=
      Nat.le_mul_of_pos_right (B + D) positive
    have expand : (C + B + D) * (post - start) =
        C * (post - start) + (B + D) * (post - start) := by
      rw [Nat.add_assoc, Nat.add_mul]
    rw [expand]
    omega

/-- Gas-amortization contract for one funded loop. `condition` and `loopBody` are
the actual loop's guard and body.

The first record is the per-iteration body contract, stated over the exact
`StatementRun` events, so straight-line declarations, every executed expression,
memory access and structured copy are charged, not only calls and iterations:
`mu` never decreases; it advances by at least one unit on every *continuing*
iteration (results `none` and `continue`, the only paths that come back to the
guard) because such a path performed an actual positive `charge_gas` debit;
and every body run costs at most `C` per consumed unit plus one fixed prefix `B`
(the terminal/rejection prefix that need not have charged anything).

The second record is the fixed per-iteration overhead: the loop statement entry
together with the guard expression's own events costs at most `D`. The guard is
charged on every evaluation, including the final false one.

Both records are restricted to the allowed states `I` — the funded, laid-out,
code-installed and reachable states the real guest actually runs in. An
all-states contract is not dischargeable from the funded-state lemmas: on an
arbitrary memory the `used` cell can wrap, the code table need not contain
`charge_gas`, and the typed cells need not exist. `I` is preserved on every
continuing successor, so the recursive loop run stays inside it. -/
def GasAmortizedBody (coeff : Work) (condition : ExpHOL 64) (loopBody : ProgHOL 64)
    (I : PanSemStateFiniteExact 64 F → Prop)
    (μ : PanSemStateFiniteExact 64 F → Nat) (C B D : Nat) : Prop :=
  (∀ (state middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (events : List WorkEvent),
      I state → StatementRun state loopBody result middle events →
        μ state ≤ μ middle ∧
        (result = none ∨ result = some .continue → μ state + 1 ≤ μ middle) ∧
        (result = none ∨ result = some .continue → I middle) ∧
        coeff.score (executionWork events) ≤ C * (μ middle - μ state) + B) ∧
  (∀ (state : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (events : List WorkEvent),
      I state → CostedExpressionRun state condition value events →
        coeff.score (executionWork (WorkEvent.statement :: events)) ≤ D)

/-- Program-indexed loop budget: the amortized statement for a loop program, and
`True` for every other constructor. Indexing the budget by the program is what
makes the direct induction on the exact `StatementRun` derivation possible. -/
def LoopBudget (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat) (C B D : Nat)
    (s post : PanSemStateFiniteExact 64 F) (events : List WorkEvent) (p : ProgHOL 64) : Prop :=
  match p with
  | .while _ _ =>
      coeff.score (executionWork events) ≤ (C + B + D) * (μ post - μ s) + (B + D) ∧
      μ s ≤ μ post
  | _ => True

/-- Core gas amortization for a source loop, proved directly on the exact
`StatementRun` trace. If each body iteration pays at most `C` per unit of the
consumed funding measure and `D` of guard/statement overhead, then a complete
loop run pays `(C + D) * (mu post - mu s) + D`, and the measure never decreases
along the loop. The bound mentions only the funding this run actually consumed:
no program, frame, ROM or bitmap size, and no `2^64` fallback, appears. Terminal
paths (break, propagating result, timeout, malformed guard) keep their executed
prefix. -/
theorem while_gas_budget_core (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat)
    (I : PanSemStateFiniteExact 64 F → Prop) (C B D : Nat)
    (clockStep : ∀ state : PanSemStateFiniteExact 64 F, I state → I (decClockHOLFinite state))
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s p r post events)
    (initial : I s)
    (amortized : ∀ (condition : ExpHOL 64) (body : ProgHOL 64), p = .while condition body →
      GasAmortizedBody coeff condition body I μ C B D) :
    LoopBudget coeff μ C B D s post events p := by
  induction run with
  | skip => trivial
  | seqNext _ _ _ _ => trivial
  | seqStop _ _ _ => trivial
  | iteYes _ _ _ => trivial
  | iteNo _ _ => trivial
  | breakStmt => trivial
  | continueStmt => trivial
  | @whileFalse state condition body guardEvents guard =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  | @whileNext state condition body value guardEvents middle result post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepMono, stepProgress, stepPreserve, stepCost⟩ :=
      steps _ _ _ _ (clockStep state initial) one
    obtain ⟨restBound, restMono⟩ := ihRest (stepPreserve (by simp)) amortized
    simp only [clockInvariant] at stepMono stepProgress stepCost
    have progress : μ state + 1 ≤ μ middle := stepProgress (by simp)
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents ++ restEvents)
    have splitFirst := executionWork_score_append coeff guardEvents (bodyEvents ++ restEvents)
    have splitSecond := executionWork_score_append coeff bodyEvents restEvents
    have arithmetic := gas_budget_continue_arith (start := μ state) (middle := μ middle)
      (post := μ post) (C := C) (B := B) (D := D) (by omega) progress
    refine ⟨?_, by omega⟩
    rw [splitStatement, List.append_assoc, splitFirst, splitSecond]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileContinue state condition body value guardEvents middle result post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepMono, stepProgress, stepPreserve, stepCost⟩ :=
      steps _ _ _ _ (clockStep state initial) one
    obtain ⟨restBound, restMono⟩ := ihRest (stepPreserve (by simp)) amortized
    simp only [clockInvariant] at stepMono stepProgress stepCost
    have progress : μ state + 1 ≤ μ middle := stepProgress (by simp)
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents ++ restEvents)
    have splitFirst := executionWork_score_append coeff guardEvents (bodyEvents ++ restEvents)
    have splitSecond := executionWork_score_append coeff bodyEvents restEvents
    have arithmetic := gas_budget_continue_arith (start := μ state) (middle := μ middle)
      (post := μ post) (C := C) (B := B) (D := D) (by omega) progress
    refine ⟨?_, by omega⟩
    rw [splitStatement, List.append_assoc, splitFirst, splitSecond]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileBreak state condition body value guardEvents post bodyEvents guard nonzero clock one =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepMono, stepProgress, stepPreserve, stepCost⟩ :=
      steps _ _ _ _ (clockStep state initial) one
    simp only [clockInvariant] at stepMono stepCost
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents)
    have splitFirst := executionWork_score_append coeff guardEvents bodyEvents
    have arithmetic := gas_budget_terminal_arith (start := μ state) (post := μ post)
      (C := C) (B := B) (D := D) (by omega)
    refine ⟨?_, by omega⟩
    rw [splitStatement, splitFirst]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileTimeout state condition body value guardEvents guard nonzero clock =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, by simpa only [resetInvariant] using Nat.le_refl (μ state)⟩
    simp only [resetInvariant]
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  | @whileMissingGuard state condition body guardEvents guard =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  | @whilePropagate state condition body value guardEvents post bodyEvents result
      guard nonzero clock notBreak notContinue one =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepMono, stepProgress, stepPreserve, stepCost⟩ :=
      steps _ _ _ _ (clockStep state initial) one
    simp only [clockInvariant] at stepMono stepCost
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents)
    have splitFirst := executionWork_score_append coeff guardEvents bodyEvents
    have arithmetic := gas_budget_terminal_arith (start := μ state) (post := μ post)
      (C := C) (B := B) (D := D) (by omega)
    refine ⟨?_, by omega⟩
    rw [splitStatement, splitFirst]
    refine Nat.le_trans ?_ arithmetic
    omega
  | assignValue _ _ => trivial
  | assignInvalid _ _ => trivial
  | assignFailure _ => trivial
  | returnValue _ _ => trivial
  | returnOversize _ _ => trivial
  | returnFailure _ => trivial
  | raiseValue _ _ _ _ => trivial
  | raiseFailure _ => trivial
  | storeValue _ _ _ => trivial
  | storeRejected _ _ _ => trivial
  | storeSourceFailure _ _ => trivial
  | storeAddressFailure _ => trivial
  | store32Value _ _ _ => trivial
  | store32Rejected _ _ _ => trivial
  | storeByteValue _ _ _ => trivial
  | storeByteRejected _ _ _ => trivial
  | declareValue _ _ _ _ => trivial
  | declareMismatch _ _ => trivial
  | declareFailure _ => trivial
  | callDone _ _ _ _ _ _ => trivial
  | callHandler _ _ _ _ _ _ _ _ => trivial
  | callArgumentsFailure _ => trivial
  | callLookupFailure _ _ => trivial
  | callTimeout _ _ _ => trivial
  | declareCallReturn _ _ _ _ _ _ _ => trivial
  | declareCallArgumentsFailure _ => trivial
  | declareCallLookupFailure _ _ => trivial
  | declareCallTimeout _ _ _ => trivial
  | declareCallRejectedReturn _ _ _ _ _ _ => trivial
  | declareCallStopped _ _ _ _ _ _ => trivial
  | tickStep _ => trivial
  | tickTimeout _ => trivial
  | annotation => trivial
  | iteInvalidGuard _ _ => trivial
  | @whileInvalidGuard state condition body value events guard invalid =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ initial guard
    have splitGuard := executionWork_score_cons coeff .statement events
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  | storeInvalidAddress _ _ => trivial
  | store32InvalidAddress _ _ => trivial
  | storeByteInvalidAddress _ _ => trivial
  | store32InvalidValue _ _ _ => trivial
  | storeByteInvalidValue _ _ _ => trivial
  | primitiveValue _ _ _ => trivial
  | primitiveInvalid _ _ _ => trivial
  | primitiveRejected _ _ => trivial
  | primitiveArgumentsFailure _ => trivial
  | raiseUndeclared _ _ => trivial
  | raiseRejectedValue _ _ _ => trivial
  | external _ => trivial
  | sharedLoad _ => trivial
  | sharedStore _ => trivial

/-- Gas amortization for one complete loop run. -/
theorem while_gas_budget (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat)
    (I : PanSemStateFiniteExact 64 F → Prop) (C B D : Nat)
    (clockStep : ∀ state : PanSemStateFiniteExact 64 F, I state → I (decClockHOLFinite state))
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s (.while condition body) r post events)
    (initial : I s)
    (amortized : GasAmortizedBody coeff condition body I μ C B D) :
    coeff.score (executionWork events) ≤ (C + B + D) * (μ post - μ s) + (B + D) ∧
    μ s ≤ μ post :=
  while_gas_budget_core coeff μ I C B D clockStep clockInvariant resetInvariant run initial
    (fun condition' body' same => by cases same; exact amortized)

/-- A measure read from memory is untouched by the two state edits the exact
loop semantics performs: `dec_clock` (clock only) and `empty_locals` (locals
only). This is what lets the funding measure `GasFunding.used` be used directly
as the amortization measure. -/
theorem memory_measure_clock_invariant {σ : Type} [NeZero 64]
    (read : (RiscV.Word 64 → HolWordLab 64) → Nat) (s : PanSemStateFiniteExact 64 σ) :
    read (decClockHOLFinite s).memory = read s.memory := rfl

theorem memory_measure_reset_invariant {σ : Type} [NeZero 64]
    (read : (RiscV.Word 64 → HolWordLab 64) → Nat) (s : PanSemStateFiniteExact 64 σ) :
    read (emptyLocalsHOLFinite s).memory = read s.memory := rfl

/-- Gas amortization with a memory-read funding measure: the concrete shape in
which the guest's `GasFunding.used` counter enters the loop bound. -/
theorem while_gas_budget_memory {σ : Type} [NeZero 64] (coeff : Work)
    (read : (RiscV.Word 64 → HolWordLab 64) → Nat)
    (I : PanSemStateFiniteExact 64 σ → Prop) (C B D : Nat)
    (clockStep : ∀ state : PanSemStateFiniteExact 64 σ, I state → I (decClockHOLFinite state))
    {s : PanSemStateFiniteExact 64 σ} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 σ}
    {events : List WorkEvent}
    (run : StatementRun s (.while condition body) r post events)
    (initial : I s)
    (amortized : @GasAmortizedBody σ coeff condition body I (fun state => read state.memory) C B D) :
    coeff.score (executionWork events) ≤
      (C + B + D) * (read post.memory - read s.memory) + (B + D) ∧
    read s.memory ≤ read post.memory :=
  while_gas_budget coeff (fun state => read state.memory) I C B D clockStep
    (memory_measure_clock_invariant read) (memory_measure_reset_invariant read) run initial amortized

/-- Numeric ceiling: the run's executed work is at most `N` whenever the funding
measure it consumed is at most `G` and `(C + D) * G + D ≤ N`. No program, frame,
ROM or bitmap size appears, so this is a genuine per-site ceiling. -/
theorem while_gas_ceiling (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat)
    (I : PanSemStateFiniteExact 64 F → Prop) (C B D G N : Nat)
    (clockStep : ∀ state : PanSemStateFiniteExact 64 F, I state → I (decClockHOLFinite state))
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s (.while condition body) r post events)
    (initial : I s)
    (amortized : GasAmortizedBody coeff condition body I μ C B D)
    (budget : μ post ≤ G) (ceiling : (C + B + D) * G + (B + D) ≤ N) :
    coeff.score (executionWork events) ≤ N := by
  obtain ⟨bound, mono⟩ := while_gas_budget coeff μ I C B D clockStep clockInvariant
    resetInvariant run initial amortized
  have consumed : μ post - μ s ≤ G := by omega
  have monoCost : (C + B + D) * (μ post - μ s) ≤ (C + B + D) * G :=
    Nat.mul_le_mul_left _ consumed
  omega

/-- The declared challenge gas budget alone: if the whole per-unit source weight
`C + B + D` stays under `4499` and the fixed overhead `B + D` is under `4499`,
then a loop whose funding measure ends under `200000000` costs at most
`900000000000` executed work units. Note that this is a *source work vector*
ceiling: the compiler-weighted native coefficient table and the separate
non-gas budget (initialization, input decoding, bootstrap, terminal overhead)
must still be reserved by the integrating certificate. -/
theorem challenge_gas_ceiling (C B D : Nat) (small : C + B + D ≤ 4499)
    (fixed : B + D ≤ 4499) :
    (C + B + D) * 200000000 + (B + D) ≤ 900000000000 := by
  have scaled : (C + B + D) * 200000000 ≤ 4499 * 200000000 :=
    Nat.mul_le_mul_right 200000000 small
  have definite : B + D ≤ 4499 := fixed
  have numeric : 4499 * 200000000 + 4499 ≤ 900000000000 := by decide
  exact Nat.le_trans (Nat.add_le_add scaled definite) numeric

#print axioms while_gas_budget
#print axioms while_gas_budget_memory
#print axioms while_gas_ceiling
#print axioms challenge_gas_ceiling
#print axioms gas_budget_continue_arith
#print axioms gas_budget_terminal_arith
end InitECandidate.Runtime.FineCost

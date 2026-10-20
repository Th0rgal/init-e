import InitECandidate.Runtime.PanCostTotal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- Score of one statement-entry event: the statement coefficient only. -/
theorem score_statement_event (coeff : Work) :
    coeff.score (WorkEvent.statement).units = coeff.statements := by
  simp [Work.score, WorkEvent.units]

/-- Pure arithmetic core of gas amortization. `start`, `middle` and `post` are
successive values of the funding measure: the body of one iteration raises it
from `start` to `middle` (by at least one), and the remaining loop raises it to
`post`. If the body pays `C` per unit and every iteration costs the fixed
overhead `D`, the recorded costs fit under `(C + D) * (post - start) + D`. -/
theorem gas_budget_arith {start middle post C D : Nat}
    (hmono : middle ≤ post) (hprogress : start + 1 ≤ middle) :
    C * (middle - start) + ((C + D) * (post - middle) + D) + D ≤
      (C + D) * (post - start) + D := by
  have delta : post - start = (middle - start) + (post - middle) := by omega
  have split : (C + D) * ((middle - start) + (post - middle)) =
      (C + D) * (middle - start) + (C + D) * (post - middle) := Nat.mul_add _ _ _
  have inner : (C + D) * (middle - start) = C * (middle - start) + D * (middle - start) :=
    Nat.add_mul _ _ _
  have slack : D ≤ D * (middle - start) := Nat.le_mul_of_pos_right D (by omega)
  rw [delta, split, inner]
  omega

/-- A single funded iteration: one body step plus its fixed overhead fits under
`(C + D)` per consumed unit. -/
theorem gas_iteration_arith {start post C D : Nat} (hprogress : start + 1 ≤ post) :
    C * (post - start) + D ≤ (C + D) * (post - start) + D := by
  have expand : (C + D) * (post - start) =
      C * (post - start) + D * (post - start) := Nat.add_mul _ _ _
  have slack : D ≤ D * (post - start) := Nat.le_mul_of_pos_right D (by omega)
  rw [expand]
  omega

/-- Gas-amortization hypothesis for one funded loop. `condition` and `loopBody`
are the actual loop's guard and body.

The first conjunct is the per-iteration gas contract: every run of the body from
any state spends at least one unit of the funding measure `mu` (the `amount`
actually debited by `charge_gas`, not the Pancake semantic clock), and the whole
executed event list of that body costs at most `C` per spent unit. It is a
statement about the *actual* `StatementRun` events, so straight-line
declarations, every executed expression, memory access and structured copy are
charged, not merely calls and loop iterations.

The second conjunct is the per-iteration fixed overhead: the loop statement
entry together with the guard expression's own events costs at most `D`; the
guard is charged on every evaluation, including the final false one. -/
def GasAmortizedBody (coeff : Work) (condition : ExpHOL 64) (loopBody : ProgHOL 64)
    (μ : PanSemStateFiniteExact 64 F → Nat) (C D : Nat) : Prop :=
  (∀ (state middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (events : List WorkEvent),
      StatementRun state loopBody result middle events →
        μ state + 1 ≤ μ middle ∧
        coeff.score (executionWork events) ≤ C * (μ middle - μ state)) ∧
  (∀ (state : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (events : List WorkEvent),
      CostedExpressionRun state condition value events →
        coeff.score (executionWork (WorkEvent.statement :: events)) ≤ D)

/-- Program-indexed loop budget: the amortized statement for a loop program, and
`True` for every other constructor. Indexing the budget by the program is what
makes the direct induction on the exact `StatementRun` derivation possible. -/
def LoopBudget (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat) (C D : Nat)
    (s post : PanSemStateFiniteExact 64 F) (events : List WorkEvent) (p : ProgHOL 64) : Prop :=
  match p with
  | .while _ _ =>
      coeff.score (executionWork events) ≤ (C + D) * (μ post - μ s) + D ∧ μ s ≤ μ post
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
    (C D : Nat)
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s p r post events)
    (amortized : ∀ (condition : ExpHOL 64) (body : ProgHOL 64), p = .while condition body →
      GasAmortizedBody coeff condition body μ C D) :
    LoopBudget coeff μ C D s post events p := by
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
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    omega
  | @whileNext state condition body value guardEvents middle result post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepProgress, stepCost⟩ := steps _ _ _ _ one
    obtain ⟨restBound, restMono⟩ := ihRest amortized
    simp only [clockInvariant] at stepProgress stepCost
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents ++ restEvents)
    have splitFirst := executionWork_score_append coeff guardEvents (bodyEvents ++ restEvents)
    have splitSecond := executionWork_score_append coeff bodyEvents restEvents
    have arithmetic := gas_budget_arith (start := μ state) (middle := μ middle) (post := μ post)
      (C := C) (D := D) (by omega) (by omega)
    refine ⟨?_, by omega⟩
    rw [splitStatement, List.append_assoc, splitFirst, splitSecond]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileContinue state condition body value guardEvents middle result post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepProgress, stepCost⟩ := steps _ _ _ _ one
    obtain ⟨restBound, restMono⟩ := ihRest amortized
    simp only [clockInvariant] at stepProgress stepCost
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents ++ restEvents)
    have splitFirst := executionWork_score_append coeff guardEvents (bodyEvents ++ restEvents)
    have splitSecond := executionWork_score_append coeff bodyEvents restEvents
    have arithmetic := gas_budget_arith (start := μ state) (middle := μ middle) (post := μ post)
      (C := C) (D := D) (by omega) (by omega)
    refine ⟨?_, by omega⟩
    rw [splitStatement, List.append_assoc, splitFirst, splitSecond]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileBreak state condition body value guardEvents post bodyEvents guard nonzero clock one =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepProgress, stepCost⟩ := steps _ _ _ _ one
    simp only [clockInvariant] at stepProgress stepCost
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents)
    have splitFirst := executionWork_score_append coeff guardEvents bodyEvents
    have arithmetic := gas_iteration_arith (start := μ state) (post := μ post) (C := C) (D := D)
      (by omega)
    refine ⟨?_, by omega⟩
    rw [splitStatement, splitFirst]
    refine Nat.le_trans ?_ arithmetic
    omega
  | @whileTimeout state condition body value guardEvents guard nonzero clock =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, by simpa only [resetInvariant] using Nat.le_refl (μ state)⟩
    simp only [resetInvariant]
    rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    omega
  | @whileMissingGuard state condition body guardEvents guard =>
    simp only [LoopBudget]
    obtain ⟨_, guards⟩ := amortized _ _ rfl
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement guardEvents
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    omega
  | @whilePropagate state condition body value guardEvents post bodyEvents result
      guard nonzero clock notBreak notContinue one =>
    simp only [LoopBudget]
    obtain ⟨steps, guards⟩ := amortized _ _ rfl
    obtain ⟨stepProgress, stepCost⟩ := steps _ _ _ _ one
    simp only [clockInvariant] at stepProgress stepCost
    have guardBound := guards _ _ _ guard
    have splitGuard := executionWork_score_cons coeff .statement guardEvents
    have statementCost := score_statement_event coeff
    have splitStatement := executionWork_score_cons coeff .statement (guardEvents ++ bodyEvents)
    have splitFirst := executionWork_score_append coeff guardEvents bodyEvents
    have arithmetic := gas_iteration_arith (start := μ state) (post := μ post) (C := C) (D := D)
      (by omega)
    refine ⟨Nat.le_trans ?_ arithmetic, by omega⟩
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
    have guardBound := guards _ _ _ guard
    have guardSplit := executionWork_score_cons coeff .statement events
    have statementCost := score_statement_event coeff
    refine ⟨?_, Nat.le_refl _⟩
    rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
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
    (C D : Nat)
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s (.while condition body) r post events)
    (amortized : GasAmortizedBody coeff condition body μ C D) :
    coeff.score (executionWork events) ≤ (C + D) * (μ post - μ s) + D ∧ μ s ≤ μ post :=
  while_gas_budget_core coeff μ C D clockInvariant resetInvariant run
    (fun condition body same => by
      cases same
      exact amortized)


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
    (C D : Nat)
    {s : PanSemStateFiniteExact 64 σ} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 σ}
    {events : List WorkEvent}
    (run : StatementRun s (.while condition body) r post events)
    (amortized : @GasAmortizedBody σ coeff condition body (fun state => read state.memory) C D) :
    coeff.score (executionWork events) ≤
      (C + D) * (read post.memory - read s.memory) + D ∧
    read s.memory ≤ read post.memory :=
  while_gas_budget coeff (fun state => read state.memory) C D
    (memory_measure_clock_invariant read) (memory_measure_reset_invariant read) run amortized

/-- Numeric ceiling: the run's executed work is at most `N` whenever the funding
measure it consumed is at most `G` and `(C + D) * G + D ≤ N`. No program, frame,
ROM or bitmap size appears, so this is a genuine per-site ceiling. -/
theorem while_gas_ceiling (coeff : Work) (μ : PanSemStateFiniteExact 64 F → Nat)
    (C D G N : Nat)
    (clockInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (decClockHOLFinite state) = μ state)
    (resetInvariant : ∀ state : PanSemStateFiniteExact 64 F,
      μ (emptyLocalsHOLFinite state) = μ state)
    {s : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {events : List WorkEvent} (run : StatementRun s (.while condition body) r post events)
    (amortized : GasAmortizedBody coeff condition body μ C D)
    (budget : μ post ≤ G) (ceiling : (C + D) * G + D ≤ N) :
    coeff.score (executionWork events) ≤ N := by
  obtain ⟨bound, mono⟩ := while_gas_budget coeff μ C D clockInvariant resetInvariant run amortized
  have consumed : μ post - μ s ≤ G := by omega
  have monoCost : (C + D) * (μ post - μ s) ≤ (C + D) * G :=
    Nat.mul_le_mul_left _ consumed
  omega

/-- The declared challenge gas budget alone: with a per-unit cost `C + D` under
`4499` and the conservative `+ D` slack, a loop whose funding measure ends under
`200000000` costs at most `900000000000` executed work units. -/
theorem challenge_gas_ceiling (C D : Nat) (small : C + D ≤ 4499) :
    (C + D) * 200000000 + D ≤ 900000000000 := by
  have scaled : (C + D) * 200000000 ≤ 4499 * 200000000 :=
    Nat.mul_le_mul_right 200000000 small
  have definite : D ≤ 4499 := by omega
  have numeric : 4499 * 200000000 + 4499 ≤ 900000000000 := by decide
  exact Nat.le_trans (Nat.add_le_add scaled definite) numeric

#print axioms while_gas_budget
#print axioms while_gas_budget_memory
#print axioms while_gas_ceiling
#print axioms challenge_gas_ceiling
#print axioms gas_budget_arith
end InitECandidate.Runtime.FineCost

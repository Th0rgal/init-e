import InitECandidate.Runtime.SourceCost
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- **Key adapter**: the existing `ProgBounded` machinery already proves the hard part (a run from a
large enough clock spends at most `cost` ticks and does not time out). The all-outcome `CostBounded`
follows by cases: at a large clock use the bounded run; at a small clock the post clock is
non-negative, so `state.clock < cost ≤ cost + post.clock` holds trivially. -/
theorem costBounded_of_progBounded (program : ProgHOL 64) (cost : Nat)
    (bounded : ProgBounded program cost) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost := by
  intro F state code
  by_cases enough : cost ≤ state.clock
  · exact (bounded state code enough).1
  · have small : state.clock < cost := by omega
    have nonneg : 0 ≤ (evaluateHOLFiniteState state program).2.clock := Nat.zero_le _
    omega

/-- The same adapter for the per-state `RunBounded` form: no code premise needed. -/
theorem costBounded_of_runBounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (cost : Nat) (bounded : RunBounded state program cost) :
    state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost := bounded.1

/-- A `.call` may also be bounded after its callee, using `FunBounded`. -/
theorem costBounded_call_of_funBounded {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      state.clock ≤ (evaluateHOLFiniteState state
        (.call (some (destination,none)) function arguments)).2.clock + (cost + 1) :=
  costBounded_of_progBounded _ _ (ProgBounded.call installed destination arguments)

/-- The allocator call, reusing the existing uniform bound (no `FunBounded` needed for `alloc`). -/
theorem costBounded_allocCall (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      state.clock ≤ (evaluateHOLFiniteState state
        (.call (some (destination,none)) (ofString "alloc") arguments)).2.clock + 2 :=
  costBounded_of_progBounded _ _ (ProgBounded.alloc destination arguments)

/-- Sequential composition of the all-outcome bounds (the `CostBounded` form of
`ProgBounded.seq`). -/
theorem costBounded_seq' {F : Type} (state : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    {a b : Nat} (code : state.code = originalRuntimeCode)
    (left : ProgBounded first a) (right : ProgBounded tail b)
    (budget : a + b ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state (.seq first tail)).2.clock + (a + b) :=
  (RunBounded.seq (RunBounded.ofProg left code (by omega)) budget
    (fun next run nextCode nextBudget => RunBounded.ofProg right (nextCode.trans code) nextBudget)).1

#print axioms costBounded_of_progBounded
#print axioms costBounded_call_of_funBounded
#print axioms costBounded_allocCall
#print axioms costBounded_seq'
end InitECandidate.Runtime

import InitECandidate.Runtime.WordStackValueCostBasis

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 4000000

theorem stack_value_cost_ite {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (yes no : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (left : StackValueCostGoal price yes source) (right : StackValueCostGoal price no source) :
    StackValueCostGoal price (.ite cmp reg operand yes no) source := by
  intro safe stack related
  have get : getVar reg {source with stack := stack} = getVar reg source := rfl
  have imm : getVarImm operand {source with stack := stack} = getVarImm operand source := by
    cases operand <;> rfl
  rw [evaluate] at safe
  rcases lhs : getVar reg source with _ | x
  · simp only [lhs] at safe
    exact (safe rfl).elim
  rcases rhs : getVarImm operand source with _ | y
  · simp only [lhs, rhs] at safe
    exact (safe rfl).elim
  rcases comparison : wordSemWordCmp cmp x y with _ | selected
  · simp only [lhs, rhs, comparison] at safe
    exact (safe rfl).elim
  simp only [lhs, rhs, comparison] at safe
  conv_lhs => rw [wordExecutionCost]
  conv_rhs => rw [wordExecutionCost]
  simp only [get, imm, lhs, rhs, comparison]
  cases selected with
  | false => exact congrArg (fun n => price (.ite cmp reg operand yes no) + n) (right safe stack related)
  | true => exact congrArg (fun n => price (.ite cmp reg operand yes no) + n) (left safe stack related)

theorem stack_value_cost_mustTerminate {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (inner : source.termdep ≠ 0 → StackValueCostGoal price body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}) :
    StackValueCostGoal price (.mustTerminate body) source := by
  intro safe stack related
  by_cases zero : source.termdep = 0
  · rw [evaluate, dif_pos zero] at safe
    exact (safe rfl).elim
  let entry : WordSemStateFiniteExact 64 C F :=
    {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
  rcases actual : evaluate body entry with ⟨result, post⟩
  have sourceEq := WordToWord.evaluate_mustTerminate_run body source zero result post actual
  have noTimeout : result ≠ some .timeOut := by
    intro bad
    rw [sourceEq, if_pos bad] at safe
    exact (safe rfl).elim
  have bodySafe : (evaluate body entry).1 ≠ some .error := by
    rw [actual]
    rw [sourceEq, if_neg noTimeout] at safe
    exact safe
  have cost := inner zero bodySafe stack related
  conv_lhs => rw [wordExecutionCost]
  conv_rhs => rw [wordExecutionCost]
  simp only [dif_neg zero]
  exact congrArg (fun n => price (.mustTerminate body) + n) cost

/-- Continuing loop-body outcomes transport by a stack-only post update. -/
theorem stack_value_continuing {C F : Type} (body : WordLangProgHOL (BitVec 64))
    (source post : WordSemStateFiniteExact 64 C F) (result : Option (WordSemResult 64))
    (stack : List (WordSemStackFrame 64)) (actual : evaluate body source = (result, post))
    (related : sValEq source.stack stack) (continuing : wordSemContLoop result = true) :
    ∃ afterStack, evaluate body {source with stack := stack} = (result, {post with stack := afterStack}) ∧
      sValEq post.stack afterStack := by
  have normal : result = none ∨ result = some (.continue 0) := by
    cases result with
    | none => exact Or.inl rfl
    | some outcome =>
      cases outcome <;> simp_all [wordSemContLoop]
  rcases normal with rfl | rfl
  · exact stack_value_none body source post stack actual related
  · have transport := evaluateStackSwap body source
    unfold stackSwapPost at transport
    rw [actual] at transport
    obtain ⟨afterStack, run, values, _⟩ := transport.2.2 stack related
    exact ⟨afterStack, run, values⟩

theorem pure_loop_cost_run {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source entry post : WordSemStateFiniteExact 64 C F) (result : Option (WordSemResult 64))
    (cut : cutState (names, .ln) source = some entry) (actual : evaluate body entry = (result, post)) :
    wordExecutionCost (fun p _ => price p) (.loop names body exits) source =
      price (.loop names body exits) + wordExecutionCost (fun p _ => price p) body entry +
        if wordSemContLoop result then
          (if post.clock = 0 then 0 else wordExecutionCost (fun p _ => price p) (.loop names body exits) (decClock post))
        else 0 := by
  rw [wordExecutionCost, cut]
  dsimp only
  rw [fix_clock_evaluate, actual]
  simp only [wordSemSTOP]
  split_ifs <;> rfl

#print axioms stack_value_cost_ite
#print axioms stack_value_cost_mustTerminate
#print axioms stack_value_continuing
#print axioms pure_loop_cost_run
end InitECandidate.Runtime.FineCost

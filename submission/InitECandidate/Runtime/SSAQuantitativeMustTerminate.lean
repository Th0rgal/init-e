import InitECandidate.Runtime.SSAQuantitativeCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticMustTerminate
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- The actual bounded-depth wrapper preserves the quantitative witness.
Its body is charged at the real reset clock/decremented depth. Timeouts become
source errors exactly as in the pinned evaluator, retaining error exemption. -/
theorem ssa_quantitative_mustTerminate {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (s t : WordSemStateFiniteExact 64 C F) m n ts,
      Flapjack.WordAlloc.wordStateEqRel s t ∧ ssaLocalsRel n m s.locals t.locals ∧
      isAllocVar n ∧ everyVarHOL (fun x => decide (x < n)) body = true ∧
      ssaMapOK n m ∧ ltOK ts → SSAQuantitativeSimulation SP TP body s t m n ts)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.mustTerminate body) = true ∧
      ssaMapOK next map ∧ ltOK tables)
    (headPrice : TP (ssaCcTrans (.mustTerminate body) map next tables).1 ≤ SP (.mustTerminate body)) :
    SSAQuantitativeSimulation SP TP (.mustTerminate body) source target map next tables := by
  by_cases zero : source.termdep = 0
  · refine ⟨target.permute, Or.inl ?_⟩
    simp [evaluate, zero]
  · let innerSource := {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
    let innerTarget := {target with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
    have depth : target.termdep = source.termdep := by
      rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, depth, _, _, _, _⟩
      exact depth
    have frame : Flapjack.WordAlloc.wordStateEqRel innerSource innerTarget := by
      simp_all [innerSource, innerTarget, Flapjack.WordAlloc.wordStateEqRel]
    obtain ⟨permutation, simulation⟩ := bodyIH innerSource innerTarget map next tables
      ⟨frame, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    rcases compiledEq : ssaCcTrans body map next tables with ⟨output, mapOut, nextOut⟩
    have compileOuter : ssaCcTrans (.mustTerminate body) map next tables =
        (.mustTerminate output, mapOut, nextOut) := by
      rw [ssaCcTrans, compiledEq]
    dsimp only at simulation
    rw [compiledEq] at simulation
    rcases sourceEval : evaluate body {innerSource with permute := permutation} with ⟨result, after⟩
    rw [sourceEval] at simulation
    refine ⟨permutation, ?_⟩
    dsimp only
    rw [compileOuter]
    by_cases error : result = some .error
    · subst result
      left
      simp [evaluate, zero, sourceEval, innerSource]
    · by_cases timeout : result = some .timeOut
      · subst result
        left
        simp [evaluate, zero, sourceEval, innerSource]
      · rcases simulation with bad | ⟨same, postFrame, locals, work⟩
        · exact (error bad).elim
        rcases targetEval : evaluate output innerTarget with ⟨targetResult, targetAfter⟩
        rw [targetEval] at same postFrame locals
        have eq : targetResult = result := same.symm
        subst targetResult
        have sourceOuter : evaluate (.mustTerminate body) {source with permute := permutation} =
            (result, {after with clock := source.clock, termdep := source.termdep}) := by
          simp only [evaluate, zero]
          rw [sourceEval]
          cases result with
          | none => rfl
          | some value => cases value <;> simp_all
        have targetInner : evaluate output {target with clock := wordSemMustTerminateLimit 64, termdep := target.termdep - 1} = (result, targetAfter) := by
          simpa only [innerTarget, depth] using targetEval
        have targetOuter : evaluate (.mustTerminate output) target =
            (result, {targetAfter with clock := target.clock, termdep := target.termdep}) := by
          have targetNonzero : target.termdep ≠ 0 := by simpa only [depth] using zero
          simp only [evaluate, targetNonzero]
          rw [targetInner]
          cases result with
          | none => rfl
          | some value => cases value <;> simp_all
        rw [sourceOuter, targetOuter]
        right
        refine ⟨rfl, ?_, locals, ?_⟩
        · simp_all [Flapjack.WordAlloc.wordStateEqRel]
        · conv_lhs => rw [wordExecutionCost]
          conv_rhs => rw [wordExecutionCost]
          simp only [zero, depth, if_false]
          dsimp only at work
          have price : TP (.mustTerminate output) ≤ SP (.mustTerminate body) := by
            simpa only [compileOuter] using headPrice
          exact Nat.add_le_add price work

#print axioms ssa_quantitative_mustTerminate
end InitECandidate.Runtime.FineCost

import InitECandidate.Runtime.SSAQuantitativeSeq
import InitECandidate.Runtime.SSAQuantitativeAllowanceCore

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- The sequence head funds both child-entry allowances once. A stopped
prefix still executes no suffix; the conservative unused allowance stays
within the same local head budget. Semantics and cost use one permutation. -/
theorem ssa_quantitative_seq_fund_entries {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (first second firstOut secondOut : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map mapFirst mapSecond : Spt Nat) (next nextFirst nextSecond : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstCompiled : ssaCcTrans first map next tables = (firstOut, mapFirst, nextFirst))
    (secondCompiled : ssaCcTrans second mapFirst nextFirst tables = (secondOut, mapSecond, nextSecond))
    (firstEntry secondEntry : Nat)
    (headPrice : TP (.seq firstOut secondOut) + firstEntry + secondEntry ≤ SP (.seq first second))
    (one : SSAQuantitativeAllowance SP TP first source target map next tables firstEntry)
    (two : ∀ (s t : WordSemStateFiniteExact 64 C F),
      Flapjack.WordAlloc.wordStateEqRel s t →
      ssaLocalsRel nextFirst mapFirst s.locals t.locals →
      SSAQuantitativeAllowance SP TP second s t mapFirst nextFirst tables secondEntry) :
    SSAQuantitativeSimulation SP TP (.seq first second) source target map next tables := by
  have compiled : ssaCcTrans (.seq first second) map next tables =
      (.seq firstOut secondOut, mapSecond, nextSecond) := by
    simp only [ssaCcTrans, firstCompiled, secondCompiled]
  obtain ⟨permutation, firstSim⟩ := one
  dsimp only at firstSim
  rw [firstCompiled] at firstSim
  rcases sourceEval : evaluate first {source with permute := permutation} with ⟨result, sourceAfter⟩
  rw [sourceEval] at firstSim
  cases result with
  | some result =>
    refine ⟨permutation, ?_⟩
    dsimp only
    rw [compiled]
    rw [evaluate, fix_clock_evaluate, sourceEval]
    rcases firstSim with bad | ⟨same, frame, locals, work⟩
    · exact Or.inl bad
    · right
      rcases targetEval : evaluate firstOut target with ⟨targetResult, targetAfter⟩
      rw [targetEval] at same frame locals
      have eq : targetResult = some result := same.symm
      subst targetResult
      rw [evaluate, fix_clock_evaluate, targetEval]
      refine ⟨rfl, frame, SSAResultLocals.terminal result locals, ?_⟩
      rw [wordExecutionCost_seq, wordExecutionCost_seq, targetEval, sourceEval]
      simp only [Nat.add_zero]
      dsimp only at work
      omega
  | none =>
    rcases firstSim with bad | ⟨same, frame, locals, firstWork⟩
    · cases bad
    rcases targetEval : evaluate firstOut target with ⟨targetResult, targetAfter⟩
    rw [targetEval] at same frame locals
    have eq : targetResult = none := same.symm
    subst targetResult
    obtain ⟨secondPermutation, secondSim⟩ := two sourceAfter targetAfter frame locals
    obtain ⟨combinedPermutation, firstRun, firstCost⟩ :=
      word_permute_executed_cost SP first {source with permute := permutation}
        secondPermutation (by simp only [sourceEval]; simp)
    rw [sourceEval] at firstRun
    have firstRun' : evaluate first {source with permute := combinedPermutation} =
        (none, {sourceAfter with permute := secondPermutation}) := firstRun
    have firstCost' : wordExecutionCost (fun p _ => SP p) first
        {source with permute := combinedPermutation} =
        wordExecutionCost (fun p _ => SP p) first {source with permute := permutation} := firstCost
    refine ⟨combinedPermutation, ?_⟩
    dsimp only at secondSim ⊢
    rw [compiled]
    rw [evaluate, fix_clock_evaluate, firstRun']
    rcases secondSim with bad | ⟨sameSecond, frameSecond, localsSecond, secondWork⟩
    · exact Or.inl bad
    · right
      rw [evaluate, fix_clock_evaluate, targetEval]
      rw [secondCompiled] at sameSecond frameSecond localsSecond secondWork
      refine ⟨sameSecond, frameSecond, localsSecond, ?_⟩
      rw [wordExecutionCost_seq, wordExecutionCost_seq, targetEval, firstRun']
      simp only
      rw [firstCost']
      dsimp only at firstWork secondWork
      omega

#print axioms ssa_quantitative_allowance_zero
#print axioms ssa_quantitative_seq_fund_entries
end InitECandidate.Runtime.FineCost

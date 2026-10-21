import InitECandidate.Runtime.SSAQuantitativeCost
import InitECandidate.Runtime.WordPermuteGlobalCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- A terminal prefix does not use the sequence output map. -/
theorem SSAResultLocals.terminal {α : Type} {n m : Nat} {a b : Spt Nat}
    {tables : List (Spt Nat × Spt Unit × Spt Unit)} {s t : Spt α}
    (result : WordSemResult 64)
    (h : SSAResultLocals n a tables s t (some result)) :
    SSAResultLocals m b tables s t (some result) := by
  cases result <;> exact h

/-- Composition for the actual SSA sequence compilation. The suffix premise
is a smaller-body simulation at the exact compiler output map, and only at
states satisfying the reached prefix frame and locals relations. A single
source-permutation witness carries both semantics and executed cost. -/
theorem ssa_quantitative_seq {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (first second firstOut secondOut : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map mapFirst mapSecond : Spt Nat) (next nextFirst nextSecond : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstCompiled : ssaCcTrans first map next tables = (firstOut, mapFirst, nextFirst))
    (secondCompiled : ssaCcTrans second mapFirst nextFirst tables = (secondOut, mapSecond, nextSecond))
    (headPrice : TP (.seq firstOut secondOut) ≤ SP (.seq first second))
    (one : SSAQuantitativeSimulation SP TP first source target map next tables)
    (two : ∀ (s t : WordSemStateFiniteExact 64 C F),
      Flapjack.WordAlloc.wordStateEqRel s t →
      ssaLocalsRel nextFirst mapFirst s.locals t.locals →
      SSAQuantitativeSimulation SP TP second s t mapFirst nextFirst tables) :
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
      exact Nat.add_le_add headPrice work
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
      exact Nat.add_le_add (Nat.add_le_add headPrice firstWork) secondWork

/-- Original six SSA entry invariants suffice for sequence composition.
All suffix allocation/map/variable bounds come from the real prefix compiler;
the only remaining induction premises concern the two smaller bodies. -/
theorem ssa_quantitative_seq_original {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (first second : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstIH : ∀ (s t : WordSemStateFiniteExact 64 C F) m n ts,
      Flapjack.WordAlloc.wordStateEqRel s t ∧ ssaLocalsRel n m s.locals t.locals ∧
      isAllocVar n ∧ everyVarHOL (fun x => decide (x < n)) first = true ∧
      ssaMapOK n m ∧ ltOK ts → SSAQuantitativeSimulation SP TP first s t m n ts)
    (secondIH : ∀ (s t : WordSemStateFiniteExact 64 C F) m n ts,
      Flapjack.WordAlloc.wordStateEqRel s t ∧ ssaLocalsRel n m s.locals t.locals ∧
      isAllocVar n ∧ everyVarHOL (fun x => decide (x < n)) second = true ∧
      ssaMapOK n m ∧ ltOK ts → SSAQuantitativeSimulation SP TP second s t m n ts)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.seq first second) = true ∧
      ssaMapOK next map ∧ ltOK tables)
    (headPrice : TP (ssaCcTrans (.seq first second) map next tables).1 ≤ SP (.seq first second)) :
    SSAQuantitativeSimulation SP TP (.seq first second) source target map next tables := by
  have vars : everyVarHOL (fun x => decide (x < next)) first = true ∧
      everyVarHOL (fun x => decide (x < next)) second = true := by
    simpa only [everyVarHOL, Bool.and_eq_true] using h.2.2.2.1
  rcases firstCompiled : ssaCcTrans first map next tables with ⟨firstOut, mapFirst, nextFirst⟩
  rcases secondCompiled : ssaCcTrans second mapFirst nextFirst tables with ⟨secondOut, mapSecond, nextSecond⟩
  have invariant := ssaCcTransProps first map next tables firstOut mapFirst nextFirst
    firstCompiled ⟨h.2.2.2.2.1, h.2.2.1⟩
  apply ssa_quantitative_seq SP TP first second firstOut secondOut source target
    map mapFirst mapSecond next nextFirst nextSecond tables firstCompiled secondCompiled
  · simpa only [ssaCcTrans, firstCompiled, secondCompiled] using headPrice
  · exact firstIH source target map next tables
      ⟨h.1, h.2.1, h.2.2.1, vars.1, h.2.2.2.2⟩
  · intro s t frame locals
    apply secondIH s t mapFirst nextFirst tables
    refine ⟨frame, locals, invariant.2.1, ?_, invariant.2.2, h.2.2.2.2.2⟩
    apply Flapjack.everyVarMono _ second _
    refine ⟨?_, vars.2⟩
    intro x bound
    have : x < next := of_decide_eq_true bound
    exact decide_eq_true (Nat.lt_of_lt_of_le this invariant.1)

#print axioms SSAResultLocals.terminal
#print axioms ssa_quantitative_seq
#print axioms ssa_quantitative_seq_original
end InitECandidate.Runtime.FineCost

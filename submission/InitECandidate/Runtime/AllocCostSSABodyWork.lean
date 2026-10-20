import InitECandidate.Runtime.AllocCostSSAExecuted
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-!
# Quantitative SSA body simulation: base instruction cases

`bodySimulationRun` in the pinned SSA loop proof gives the source/target result
and state relation but no executed work bound.  This module starts the
quantitative analogue at the base instructions.

`wordControlCost` counts executed control nodes and counts a parallel move as
one node, matching `wordPathWork` rather than `wordNodeCost` (which counts move
words).  On straight fragments `wordPathWork` is bounded by this cost.  The
SSA expansion of each base instruction is straight, so its actual executed work
is bounded by a constant while the source instruction costs one node.
-/

/-- Executed node count for straight fragments: a parallel move is one node. -/
def wordControlCost : WordLangProgHOL (BitVec 64) → Nat
  | .seq first second => 1 + wordControlCost first + wordControlCost second
  | .skip | .move _ _ | .inst _ | .get _ _ | .opCurrHeap _ _ _ => 1
  | _ => 0
termination_by p => sizeOf p

theorem wordPathWork_le_controlCost_straight {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (state : WordSemStateFiniteExact 64 C F)
    (supported : wordStraightFragment p = true) :
    wordPathWork p state ≤ wordControlCost p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  all_goals try (simp only [wordPathWork, wordControlCost]; omega)
  case seq first second =>
    have firstBound := wordPathWork_le_controlCost_straight first state supported.1
    rw [wordPathWork_seq]
    simp only [wordControlCost]
    cases run : evaluate first state with
    | mk result middle =>
      cases result with
      | none =>
        have secondBound := wordPathWork_le_controlCost_straight second middle supported.2
        dsimp only
        omega
      | some value =>
        dsimp only
        omega

/-- SSA `.skip` executes exactly one node. -/
theorem ssaBody_skip_executed_le {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (ssaCcTrans (width := 64) .skip ssa next lt).1 state ≤
      wordPathWork (.skip : WordLangProgHOL (BitVec 64)) state + 0 := by
  simp [ssaCcTrans, wordPathWork]

/-- SSA `.move` executes exactly one node, like the source move. -/
theorem ssaBody_move_executed_le {C F : Type}
    (priority : Nat) (moves : List (Nat × Nat))
    (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (ssaCcTrans (width := 64) (.move priority moves) ssa next lt).1 state ≤
      wordPathWork (.move priority moves : WordLangProgHOL (BitVec 64)) state + 0 := by
  simp [ssaCcTrans, wordPathWork]

/-- SSA `.return` prepends its return move: three executed nodes against one. -/
theorem ssaBody_return_executed_le {C F : Type}
    (n : Nat) (nums : List Nat)
    (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (ssaCcTrans (width := 64) (.return n nums) ssa next lt).1 state ≤
      wordPathWork (.return n nums : WordLangProgHOL (BitVec 64)) state + 2 := by
  let nums' := nums.map (optionLookup ssa)
  let rets := (List.range nums'.length).map fun x => 2 * (x + 1)
  have hout : (ssaCcTrans (width := 64) (.return n nums) ssa next lt).1 =
      .seq (.move 0 (rets.zip nums')) (.return (optionLookup ssa n) rets) := by
    simp [ssaCcTrans, rets, nums']
  rw [hout, wordPathWork_seq]
  cases run : evaluate (.move 0 (rets.zip nums')) state with
  | mk result middle =>
    cases result <;> simp [wordPathWork] <;> omega

/-- SSA `.raise` prepends its argument move: three executed nodes against one. -/
theorem ssaBody_raise_executed_le {C F : Type}
    (n : Nat) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (ssaCcTrans (width := 64) (.raise n) ssa next lt).1 state ≤
      wordPathWork (.raise n : WordLangProgHOL (BitVec 64)) state + 2 := by
  have hout : (ssaCcTrans (width := 64) (.raise n) ssa next lt).1 =
      .seq (.move 1 [(2, optionLookup ssa n)]) (.raise 2) := by
    simp [ssaCcTrans]
  rw [hout, wordPathWork_seq]
  cases run : evaluate (.move 1 [(2, optionLookup ssa n)]) state with
  | mk result middle =>
    cases result <;> simp [wordPathWork] <;> omega

/-- Public quantitative base case for `bodySimulationRun`: Skip.  The pinned
proof gives the result/state part; the work part is exactly one source and one
target executed node. -/
theorem bodySimulationRunWork_skip {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (width := 64) .skip ssa next tables =
      (output, mapOut, nextOut))
    (simulation : ssaSimulation (width := 64) .skip source target ssa next tables) :
    ∃ permutation,
      let sourceRun := WordSemStateFiniteExact.evaluate
        (.skip : WordLangProgHOL (BitVec 64)) {source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate output target
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        wordPathWork output target ≤
          wordPathWork (.skip : WordLangProgHOL (BitVec 64))
            {source with permute := permutation} + 0 := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error :
    (WordSemStateFiniteExact.evaluate (.skip : WordLangProgHOL (BitVec 64))
      {source with permute := permutation}).1 = some .error
  · exact Or.inl error
  · right
    have hout : output = .skip := by
      have first := congrArg Prod.fst produced
      simpa [ssaCcTrans] using first.symm
    rw [produced] at related
    subst output
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_⟩
    simp [wordPathWork]

/-- Public quantitative base case for `bodySimulationRun`: Move.  A parallel
move is one executed node on both sides regardless of its list length. -/
theorem bodySimulationRunWork_move {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next priority : Nat) (moves : List (Nat × Nat))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (width := 64) (.move priority moves) ssa next tables =
      (output, mapOut, nextOut))
    (simulation : ssaSimulation (width := 64) (.move priority moves)
      source target ssa next tables) :
    ∃ permutation,
      let sourceRun := WordSemStateFiniteExact.evaluate
        (.move priority moves : WordLangProgHOL (BitVec 64))
        {source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate output target
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        wordPathWork output target ≤
          wordPathWork (.move priority moves : WordLangProgHOL (BitVec 64))
            {source with permute := permutation} + 0 := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error :
    (WordSemStateFiniteExact.evaluate (.move priority moves :
      WordLangProgHOL (BitVec 64)) {source with permute := permutation}).1 =
        some .error
  · exact Or.inl error
  · right
    have hout : output = .move priority
        (((listNextVarRename (moves.map Prod.fst) ssa next).1).zip
          (moves.map (optionLookup ssa ∘ Prod.snd))) := by
      have first := congrArg Prod.fst produced
      simpa [ssaCcTrans] using first.symm
    rw [produced] at related
    subst output
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_⟩
    simp [wordPathWork]

/-- Public quantitative base case for `bodySimulationRun`: Return. -/
theorem bodySimulationRunWork_return {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next n : Nat) (nums : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (width := 64) (.return n nums) ssa next tables =
      (output, mapOut, nextOut))
    (simulation : ssaSimulation (width := 64) (.return n nums)
      source target ssa next tables) :
    ∃ permutation,
      let sourceRun := WordSemStateFiniteExact.evaluate
        (.return n nums : WordLangProgHOL (BitVec 64))
        {source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate output target
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        wordPathWork output target ≤
          wordPathWork (.return n nums : WordLangProgHOL (BitVec 64))
            {source with permute := permutation} + 2 := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error :
    (WordSemStateFiniteExact.evaluate (.return n nums :
      WordLangProgHOL (BitVec 64)) {source with permute := permutation}).1 =
        some .error
  · exact Or.inl error
  · right
    let nums' := nums.map (optionLookup ssa)
    let rets := (List.range nums'.length).map fun x => 2 * (x + 1)
    have hout : output =
        .seq (.move 0 (rets.zip nums')) (.return (optionLookup ssa n) rets) := by
      have first := congrArg Prod.fst produced
      simpa [ssaCcTrans, rets, nums'] using first.symm
    rw [produced] at related
    subst output
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_⟩
    have ht : wordPathWork
        (.seq (.move 0 (rets.zip nums')) (.return (optionLookup ssa n) rets) :
          WordLangProgHOL (BitVec 64)) target ≤ 3 := by
      rw [wordPathWork_seq]
      cases run : evaluate (.move 0 (rets.zip nums')) target with
      | mk result middle =>
        cases result <;> simp [wordPathWork] <;> omega
    have hs : wordPathWork (.return n nums : WordLangProgHOL (BitVec 64))
        {source with permute := permutation} = 1 := by
      simp [wordPathWork]
    omega

/-- Public quantitative base case for `bodySimulationRun`: Raise. -/
theorem bodySimulationRunWork_raise {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next n : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (width := 64) (.raise n) ssa next tables =
      (output, mapOut, nextOut))
    (simulation : ssaSimulation (width := 64) (.raise n)
      source target ssa next tables) :
    ∃ permutation,
      let sourceRun := WordSemStateFiniteExact.evaluate
        (.raise n : WordLangProgHOL (BitVec 64))
        {source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate output target
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        wordPathWork output target ≤
          wordPathWork (.raise n : WordLangProgHOL (BitVec 64))
            {source with permute := permutation} + 2 := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error :
    (WordSemStateFiniteExact.evaluate (.raise n : WordLangProgHOL (BitVec 64))
      {source with permute := permutation}).1 = some .error
  · exact Or.inl error
  · right
    have hout : output = .seq (.move 1 [(2, optionLookup ssa n)]) (.raise 2) := by
      have first := congrArg Prod.fst produced
      simpa [ssaCcTrans] using first.symm
    rw [produced] at related
    subst output
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_⟩
    have ht : wordPathWork
        (.seq (.move 1 [(2, optionLookup ssa n)]) (.raise 2) :
          WordLangProgHOL (BitVec 64)) target ≤ 3 := by
      rw [wordPathWork_seq]
      cases run : evaluate (.move 1 [(2, optionLookup ssa n)]) target with
      | mk result middle =>
        cases result <;> simp [wordPathWork] <;> omega
    have hs : wordPathWork (.raise n : WordLangProgHOL (BitVec 64))
        {source with permute := permutation} = 1 := by
      simp [wordPathWork]
    omega

/-- Sequential control composition of executed body work.  This is the
compiler's `Seq` body case: both children run from the actual intermediate
states, share the first result, and their per-execution work transfers add.
The child work premises are the ordinary induction hypotheses of the pinned
`ssaCcTransCorrectSeq` proof, not a target-work oracle. -/
theorem bodyWork_seq {C F : Type}
    (firstBody secondBody firstOut secondOut : WordLangProgHOL (BitVec 64))
    (source target firstSource firstTarget : WordSemStateFiniteExact 64 C F)
    (firstBudget secondBudget : Nat)
    (sourceRun : evaluate firstBody source = (none, firstSource))
    (targetRun : evaluate firstOut target = (none, firstTarget))
    (firstWork : wordPathWork firstOut target ≤
      wordPathWork firstBody source + firstBudget)
    (secondWork : wordPathWork secondOut firstTarget ≤
      wordPathWork secondBody firstSource + secondBudget) :
    wordPathWork (.seq firstOut secondOut) target ≤
      wordPathWork (.seq firstBody secondBody) source +
        (firstBudget + secondBudget) := by
  rw [wordPathWork_seq, wordPathWork_seq, sourceRun, targetRun]
  dsimp only
  omega

/-- The literal SSA `Seq` clause decomposes into the two actual child
compilations and a sequential output.  This is the compiler control constructor
used by `bodyWork_seq`. -/
theorem ssaCcTrans_seq_output
    (first second firstOut secondOut : WordLangProgHOL (BitVec 64))
    (ssa : Spt Nat) (next : Nat) (ssaFirst : Spt Nat) (nextFirst : Nat)
    (ssaSecond : Spt Nat) (nextSecond : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstEq : ssaCcTrans (width := 64) first ssa next tables =
      (firstOut, ssaFirst, nextFirst))
    (secondEq : ssaCcTrans (width := 64) second ssaFirst nextFirst tables =
      (secondOut, ssaSecond, nextSecond)) :
    ssaCcTrans (width := 64) (.seq first second) ssa next tables =
      (WordLangProgHOL.seq firstOut secondOut, ssaSecond, nextSecond) := by
  simp only [ssaCcTrans, firstEq, secondEq]

/-- Actual compiler `Seq` body case.  `ssaCcTrans_seq_output` supplies the
literal child outputs, and `bodyWork_seq` adds the two per-execution child
budgets at the actual intermediate states. -/
theorem ssaBody_seq_executed_le {C F : Type}
    (first second firstOut secondOut : WordLangProgHOL (BitVec 64))
    (ssa : Spt Nat) (next : Nat) (ssaFirst : Spt Nat) (nextFirst : Nat)
    (ssaSecond : Spt Nat) (nextSecond : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target firstSource firstTarget : WordSemStateFiniteExact 64 C F)
    (firstBudget secondBudget : Nat)
    (firstEq : ssaCcTrans (width := 64) first ssa next tables =
      (firstOut, ssaFirst, nextFirst))
    (secondEq : ssaCcTrans (width := 64) second ssaFirst nextFirst tables =
      (secondOut, ssaSecond, nextSecond))
    (sourceRun : evaluate first source = (none, firstSource))
    (targetRun : evaluate firstOut target = (none, firstTarget))
    (firstWork : wordPathWork firstOut target ≤
      wordPathWork first source + firstBudget)
    (secondWork : wordPathWork secondOut firstTarget ≤
      wordPathWork second firstSource + secondBudget) :
    wordPathWork (ssaCcTrans (width := 64) (.seq first second) ssa next tables).1 target ≤
      wordPathWork (.seq first second) source + (firstBudget + secondBudget) := by
  rw [ssaCcTrans_seq_output first second firstOut secondOut ssa next ssaFirst
    nextFirst ssaSecond nextSecond tables firstEq secondEq]
  exact bodyWork_seq first second firstOut secondOut source target
    firstSource firstTarget firstBudget secondBudget sourceRun targetRun
    firstWork secondWork

/-- Executed `Ite` work when the actual condition selects the true branch.
The target branch is the SSA child followed by its actual reconciliation
program; both the child transfer and the inserted reconciliation charge are
paid on this execution. -/
theorem bodyWork_ite_true {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (branch elseBranch targetBranch targetElse cons : WordLangProgHOL (BitVec 64))
    (source target sourceAfter targetAfter : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64) (branchBudget consBudget : Nat)
    (sourceReg : getVar reg source = some x)
    (sourceImm : getVarImm operand source = some y)
    (targetReg : getVar reg target = some x)
    (targetImm : getVarImm operand target = some y)
    (cmpTrue : wordSemWordCmp cmp x y = some true)
    (sourceRun : evaluate branch source = (none, sourceAfter))
    (targetRun : evaluate targetBranch target = (none, targetAfter))
    (branchWork : wordPathWork targetBranch target ≤
      wordPathWork branch source + branchBudget)
    (consWork : wordPathWork cons
      (WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), targetAfter)).2 ≤ consBudget) :
    wordPathWork (.ite cmp reg operand (.seq targetBranch cons) targetElse) target ≤
      wordPathWork (.ite cmp reg operand branch elseBranch) source +
        (branchBudget + consBudget + 1) := by
  simp only [wordPathWork]
  simp only [sourceReg, sourceImm, targetReg, targetImm, cmpTrue, targetRun]
  have hfst : (WordSemStateFiniteExact.fixClock target
      ((none : Option (WordSemResult 64)), targetAfter)).1 = none := rfl
  rw [hfst]
  simp only
  have hsum := Nat.add_le_add branchWork consWork
  rw [Nat.add_assoc] at hsum
  calc
    1 + (1 + wordPathWork targetBranch target +
        wordPathWork cons
          (WordSemStateFiniteExact.fixClock target
            ((none : Option (WordSemResult 64)), targetAfter)).2) ≤
        1 + (1 + wordPathWork branch source +
          (branchBudget + consBudget)) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add_left (Nat.add_le_add_left hsum 1) 1
    _ = 1 + wordPathWork branch source +
        (branchBudget + consBudget + 1) := by
      ac_rfl

/-- Executed `Ite` work when the actual condition selects the false branch.
The false SSA branch does not receive reconciliation moves in this case. -/
theorem bodyWork_ite_false {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (branch elseBranch targetBranch targetElse : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64) (elseBudget : Nat)
    (sourceReg : getVar reg source = some x)
    (sourceImm : getVarImm operand source = some y)
    (targetReg : getVar reg target = some x)
    (targetImm : getVarImm operand target = some y)
    (cmpFalse : wordSemWordCmp cmp x y = some false)
    (elseWork : wordPathWork targetElse target ≤
      wordPathWork elseBranch source + elseBudget) :
    wordPathWork (.ite cmp reg operand targetBranch targetElse) target ≤
      wordPathWork (.ite cmp reg operand branch elseBranch) source + elseBudget := by
  simp only [wordPathWork]
  simp only [sourceReg, sourceImm, targetReg, targetImm, cmpFalse]
  omega

/-- The literal SSA `Ite` clause.  Both branch outputs and their actual
`fixInconsistencies` reconciliation programs are exposed; this is the output
shape consumed by the selected-branch executed-work cases. -/
theorem ssaCcTrans_ite_output
    (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 e2Out e3Out e2Cons e3Cons : WordLangProgHOL (BitVec 64))
    (ssa ssa2 ssa3 ssaFin : Spt Nat)
    (next nextFirst nextSecond nextFin : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ri' : WordRegImm (BitVec 64))
    (riEq : ri' = match ri with
      | .reg reg => .reg (optionLookup ssa reg)
      | .imm value => .imm value)
    (e2Eq : ssaCcTrans (width := 64) e2 ssa next tables =
      (e2Out, ssa2, nextFirst))
    (e3Eq : ssaCcTrans (width := 64) e3 ssa nextFirst tables =
      (e3Out, ssa3, nextSecond))
    (fixEq : fixInconsistencies (width := 64) (mkPrio e2Out e3Out)
      ssa2 ssa3 nextSecond = (e2Cons, e3Cons, nextFin, ssaFin)) :
    ssaCcTrans (width := 64) (.ite cmp r ri e2 e3) ssa next tables =
      (.ite cmp (optionLookup ssa r) ri' (.seq e2Out e2Cons)
        (.seq e3Out e3Cons), ssaFin, nextFin) := by
  simp only [ssaCcTrans, e2Eq, e3Eq, fixEq, riEq]
  cases ri <;> rfl

#print axioms wordControlCost
#print axioms wordPathWork_le_controlCost_straight
#print axioms ssaBody_skip_executed_le
#print axioms ssaBody_move_executed_le
#print axioms ssaBody_return_executed_le
#print axioms ssaBody_raise_executed_le
#print axioms bodySimulationRunWork_skip
#print axioms bodySimulationRunWork_move
#print axioms bodySimulationRunWork_return
#print axioms bodySimulationRunWork_raise
#print axioms bodyWork_seq
#print axioms ssaCcTrans_seq_output
#print axioms ssaBody_seq_executed_le
#print axioms bodyWork_ite_true
#print axioms bodyWork_ite_false
#print axioms ssaCcTrans_ite_output
end InitECandidate.Runtime.FineCost

import InitECandidate.Runtime.AllocCostSSAExecuted
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAGetSetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call
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

The non-returning `Call` clause is handled from the expanded `wordPathWork`
call definition: the actual source `getVars`/`wordSemBadDestArgs`/
`wordSemFindCode` selection is transferred to the compiled call through the
original `ssaLocalsRel` and `wordStateEqRel`, the inserted argument move is
charged at its actual execution, and the whole-call bound is reduced to a
transfer for the callee BODY program at the literal `callEnv` entry states.
The remaining premise is that body transfer (the recursive call obligation of a
whole-code-map induction), not the whole-call inequality.  Terminal clock,
code-lookup, bad-shape, handler-present and failed-move paths are covered
separately.  `wordPathWork` charges the parallel argument move as one control
node; the actual moved-word allowance is recorded by `wordMoveWords` in
`callNoneMove_words`, so the native composition still pays every copied word.
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

/-- One executed loop body: the target body child work plus the actual
back-edge reconciliation program.  `loopBodyFinal_executed_le` charges the
inserted back moves at the actual intermediate state; this theorem adds the
child body transfer. -/
theorem bodyWork_loopFinal {C F : Type} {β : Type}
    (sourceBody targetBody back : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (names : Spt β) (bodyBudget : Nat)
    (childWork : wordPathWork targetBody target ≤
      wordPathWork sourceBody source + bodyBudget)
    (backBound : ∀ middle : WordSemStateFiniteExact 64 C F,
      wordPathWork back middle ≤ 1 + (sptToAList names).length) :
    wordPathWork (match back with
      | .skip => targetBody
      | _ => targetBody.seq back) target ≤
      wordPathWork sourceBody source +
        (bodyBudget + ((sptToAList names).length + 2)) := by
  have finalBound := loopBodyFinal_executed_le targetBody back target names backBound
  calc
    wordPathWork (match back with
      | .skip => targetBody
      | _ => targetBody.seq back) target ≤
        wordPathWork targetBody target + ((sptToAList names).length + 2) := finalBound
    _ ≤ (wordPathWork sourceBody source + bodyBudget) +
        ((sptToAList names).length + 2) := by
      exact Nat.add_le_add_right childWork _
    _ = wordPathWork sourceBody source +
        (bodyBudget + ((sptToAList names).length + 2)) := by
      ac_rfl

/-- The literal SSA `Loop` clause, exposing the actual setup program, renamed
body, reconciliation back-edge and final loop program. -/
theorem ssaCcTrans_loop_output
    (names exits : Spt Unit) (body setup bodyOut back bodyFinal : WordLangProgHOL (BitVec 64))
    (ssa : Spt Nat) (next : Nat) (ssaRefreshed : Spt Nat) (nextRefreshed : Nat)
    (ssaNames ssaExit : Spt Unit) (ssa' : Spt Nat) (nextBody : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (setupEq : loopSetup names exits ssa next =
      (setup, ssaRefreshed, nextRefreshed))
    (namesEq : ssaNames = Flapjack.WordAlloc.applyNummapKey (optionLookup ssaRefreshed) names)
    (exitsEq : ssaExit = Flapjack.WordAlloc.applyNummapKey (optionLookup ssaRefreshed) exits)
    (bodyEq : ssaCcTrans (width := 64) body (sptInter ssaRefreshed names)
      nextRefreshed ((ssaRefreshed, names, exits) :: tables) =
        (bodyOut, ssa', nextBody))
    (bodyFinalEq : (match ssaReconcile (width := 64) ssa' ssaRefreshed names with
      | .skip => bodyOut
      | _ => bodyOut.seq (ssaReconcile (width := 64) ssa' ssaRefreshed names)) =
        bodyFinal) :
    ssaCcTrans (width := 64) (.loop names body exits) ssa next tables =
      (.seq setup (.loop ssaNames bodyFinal ssaExit),
       sptInter ssaRefreshed exits, nextBody) := by
  simp only [ssaCcTrans, setupEq, bodyEq, namesEq, exitsEq]
  split <;> simp_all

/-- `wordSemBadDestArgs` only tests whether the argument list is empty. -/
theorem wordSemBadDestArgs_congr
    (dest : Option Nat) {args args' : List Nat} (len : args.length = args'.length) :
    wordSemBadDestArgs dest args = wordSemBadDestArgs dest args' := by
  have h : args = [] ↔ args' = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, len]
  simp only [wordSemBadDestArgs, h]

theorem moveArgs_nodup (names : List Nat) :
    ((List.range names.length).map (fun x => 2 * x)).Nodup :=
  List.Nodup.map (fun a b h => by omega) List.nodup_range

/-- Concrete run of the inserted argument move `Move 1 (convArgs.zip names)`:
a successful non-error run exposes the read values and the post-move state. -/
theorem callNoneMoveRun {width : Nat} [NeZero width] {C F : Type}
    (names convArgs : List Nat) (target middle : WordSemStateFiniteExact width C F)
    (len : convArgs.length = names.length)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec width)) target =
      (none, middle)) :
    ∃ values : List (WordLocW width),
      getVars names target = some values ∧ middle = setVars convArgs values target := by
  have hfst : (convArgs.zip names).map Prod.fst = convArgs :=
    List.map_fst_zip (Nat.le_of_eq len)
  have hsnd : (convArgs.zip names).map Prod.snd = names :=
    List.map_snd_zip (Nat.le_of_eq len.symm)
  simp only [WordSemStateFiniteExact.evaluate, hfst, hsnd] at run
  split at run
  · rename_i nodup
    cases read : getVars names target with
    | none => simp only [read] at run; exact absurd run (by simp)
    | some values =>
        simp only [read] at run
        refine ⟨values, rfl, ?_⟩
        simpa only [Prod.mk.injEq, true_and] using run.symm
  · exact absurd run (by simp)

/-- Successful non-returning call, no handler, nonzero clock: the executed work
is the call node plus the actual callee body at the literal `callEnv` state. -/
theorem wordPathWork_call_none_body_eq {C F : Type}
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (clock : s.clock ≠ 0) :
    wordPathWork (.call none dest args none) s =
      1 + wordPathWork prog (callEnv args1 ss (decClock s)) := by
  rw [wordPathWork]
  simp [get, bad, find, clock]

/-- Terminal path: failed argument read costs one node. -/
theorem wordPathWork_call_none_getVars_none {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = none) :
    wordPathWork (.call none dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get]

/-- Terminal path: bad destination/argument shape costs one node. -/
theorem wordPathWork_call_none_badDest {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = true) :
    wordPathWork (.call none dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad]

/-- Terminal path: failed code lookup costs one node. -/
theorem wordPathWork_call_none_findCode_none {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) s.code s.stackSize = none) :
    wordPathWork (.call none dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find]

/-- Terminal path: a non-returning call with an exception handler is not
entered; it costs one node. -/
theorem wordPathWork_call_none_handler {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (hh : Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)
    (s : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) s.code s.stackSize =
      some (args1, prog, ss)) :
    wordPathWork (.call none dest args (some hh)) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find]

/-- Terminal path: zero clock costs one node. -/
theorem wordPathWork_call_none_clock_zero {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (clock : s.clock = 0) :
    wordPathWork (.call none dest args none) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find, clock]

/-- Target-side argument/code selection for the compiled non-returning call:
the inserted move installs exactly the source argument values, and the post-move
state keeps the source code, stack size and clock, so the callee program and
entry size selected by the target call are the source ones. -/
theorem callNone_target_selection {C F : Type}
    (ssa : Spt Nat) (next : Nat) (args names convArgs : List Nat)
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle)) :
    getVars convArgs middle = some xs ∧
      middle.code = source.code ∧ middle.stackSize = source.stackSize ∧
        middle.clock = source.clock := by
  have convLen : convArgs.length = names.length := by rw [convEq]; simp
  obtain ⟨values, read, midEq⟩ := callNoneMoveRun names convArgs target middle convLen run
  have targetRead := ssaLocalsRelGetVars args xs next ssa source target ⟨localsRel, get⟩
  rw [← namesEq] at targetRead
  have valuesEq : values = xs := by
    rw [targetRead] at read
    exact (Option.some.inj read).symm
  subst values
  obtain ⟨-, -, -, -, -, -, stackSizeEq, -, -, -, -, -, clockEq, codeEq, -, -, -, -, -, -, -⟩ := frame
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [midEq]
    exact getVarsSetVarsEq convArgs xs target
      ⟨by rw [convEq]; exact moveArgs_nodup names,
        by rw [Flapjack.WordAlloc.getVarsLength args source xs get, convEq, namesEq]; simp⟩
  · rw [midEq]; simpa only [WordSemStateFiniteExact.setVars] using codeEq
  · rw [midEq]; simpa only [WordSemStateFiniteExact.setVars] using stackSizeEq
  · rw [midEq]; simpa only [WordSemStateFiniteExact.setVars] using clockEq

/-- Quantitative non-returning call transfer, entered-body path.  The inserted
argument move is executed at the actual target state; the callee program, entry
arguments and entry size are the ones selected by the *source* lookup, and the
target lookup selects the same triple.  What remains is the child transfer for
the actual callee BODY `prog` at the literal `callEnv` entry states. -/
theorem bodyWork_call_none_body {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize =
      some (args1, prog, ss))
    (clock : source.clock ≠ 0)
    (calleeWork : wordPathWork prog (callEnv args1 ss (decClock middle)) ≤
      wordPathWork prog (callEnv args1 ss (decClock source)) + calleeBudget) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs none)) target ≤
      wordPathWork (.call none dest args none) source + (calleeBudget + 2) := by
  obtain ⟨midRead, midCode, midStackSize, midClock⟩ :=
    callNone_target_selection ssa next args names convArgs source target middle xs
      frame localsRel namesEq convEq get run
  have badLen : convArgs.length = args.length := by rw [convEq, namesEq]; simp
  have targetBad : wordSemBadDestArgs dest convArgs = false := by
    rw [wordSemBadDestArgs_congr dest badLen]; exact bad
  have targetFind : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) middle.code middle.stackSize =
      some (args1, prog, ss) := by
    rw [midCode, midStackSize]; exact find
  have targetClock : middle.clock ≠ 0 := by rw [midClock]; exact clock
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork, wordControlCost]
  rw [moveWork]
  rw [wordPathWork_call_none_body_eq dest args source xs args1 prog ss get bad find clock]
  rw [wordPathWork_call_none_body_eq dest convArgs middle xs args1 prog ss
    midRead targetBad targetFind targetClock]
  omega

/-- Terminal path: the source call has a bad destination/argument shape, and
the compiled call reproduces that test, so both sides cost one node. -/
theorem bodyWork_call_none_badDest {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = true) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs handler)) target ≤
      wordPathWork (.call none dest args handler) source + (calleeBudget + 2) := by
  obtain ⟨midRead, midCode, -, -⟩ :=
    callNone_target_selection ssa next args names convArgs source target middle xs
      frame localsRel namesEq convEq get run
  have badLen : convArgs.length = args.length := by rw [convEq, namesEq]; simp
  have targetBad : wordSemBadDestArgs dest convArgs = true := by
    rw [wordSemBadDestArgs_congr dest badLen]; exact bad
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork]
  rw [moveWork]
  rw [wordPathWork_call_none_badDest dest args handler source get bad]
  rw [wordPathWork_call_none_badDest dest convArgs handler middle midRead targetBad]
  omega

/-- Terminal path: the source code lookup fails, and the compiled call performs
the same lookup at the related state, so both sides cost one node. -/
theorem bodyWork_call_none_findCode_none {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize = none) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs handler)) target ≤
      wordPathWork (.call none dest args handler) source + (calleeBudget + 2) := by
  obtain ⟨midRead, midCode, midStackSize, -⟩ :=
    callNone_target_selection ssa next args names convArgs source target middle xs
      frame localsRel namesEq convEq get run
  have badLen : convArgs.length = args.length := by rw [convEq, namesEq]; simp
  have targetBad : wordSemBadDestArgs dest convArgs = false := by
    rw [wordSemBadDestArgs_congr dest badLen]; exact bad
  have targetFind : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) middle.code middle.stackSize = none := by
    rw [midCode, midStackSize]; exact find
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork]
  rw [moveWork]
  rw [wordPathWork_call_none_findCode_none dest args handler source get bad find]
  rw [wordPathWork_call_none_findCode_none dest convArgs handler middle midRead targetBad targetFind]
  omega

/-- Terminal path: a non-returning call carrying an exception handler is not
entered, and the compiled call keeps that handler. -/
theorem bodyWork_call_none_handler {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (hh : Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize =
      some (args1, prog, ss)) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs (some hh))) target ≤
      wordPathWork (.call none dest args (some hh)) source + (calleeBudget + 2) := by
  obtain ⟨midRead, midCode, midStackSize, -⟩ :=
    callNone_target_selection ssa next args names convArgs source target middle xs
      frame localsRel namesEq convEq get run
  have badLen : convArgs.length = args.length := by rw [convEq, namesEq]; simp
  have targetBad : wordSemBadDestArgs dest convArgs = false := by
    rw [wordSemBadDestArgs_congr dest badLen]; exact bad
  have targetFind : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) middle.code middle.stackSize =
      some (args1, prog, ss) := by
    rw [midCode, midStackSize]; exact find
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork]
  rw [moveWork]
  rw [wordPathWork_call_none_handler dest args hh source get bad find]
  rw [wordPathWork_call_none_handler dest convArgs hh middle midRead targetBad targetFind]
  omega

/-- Terminal path: zero clock.  The compiled call is at the same clock, so it
also returns `timeOut` at cost one. -/
theorem bodyWork_call_none_clock_zero {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize =
      some (args1, prog, ss))
    (clock : source.clock = 0) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs none)) target ≤
      wordPathWork (.call none dest args none) source + (calleeBudget + 2) := by
  obtain ⟨midRead, midCode, midStackSize, midClock⟩ :=
    callNone_target_selection ssa next args names convArgs source target middle xs
      frame localsRel namesEq convEq get run
  have badLen : convArgs.length = args.length := by rw [convEq, namesEq]; simp
  have targetBad : wordSemBadDestArgs dest convArgs = false := by
    rw [wordSemBadDestArgs_congr dest badLen]; exact bad
  have targetFind : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) middle.code middle.stackSize =
      some (args1, prog, ss) := by
    rw [midCode, midStackSize]; exact find
  have targetClock : middle.clock = 0 := by rw [midClock]; exact clock
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork]
  rw [moveWork]
  rw [wordPathWork_call_none_clock_zero dest args source get bad find clock]
  rw [wordPathWork_call_none_clock_zero dest convArgs middle midRead targetBad targetFind targetClock]
  omega

/-- Terminal path: the inserted argument move itself fails on the target, so no
callee body is entered.  Two executed nodes against at least one source node. -/
theorem bodyWork_call_none_move_fails {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (names convArgs : List Nat)
    (source target : WordSemStateFiniteExact 64 C F)
    (result : WordSemResult 64) (middle : WordSemStateFiniteExact 64 C F)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (some result, middle))
    (calleeBudget : Nat) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs handler)) target ≤
      wordPathWork (.call none dest args handler) source + (calleeBudget + 2) := by
  rw [wordPathWork_seq, run]
  dsimp only
  have moveWork : wordPathWork (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64))
      target = 1 := by simp only [wordPathWork]
  rw [moveWork]
  have sourceWork := one_le_wordPathWork (.call none dest args handler) source
  omega

/-- Moved-word accounting for the inserted argument move: `wordPathWork`
charges the parallel move as one control node, while the native composition
pays every actually moved word.  This is the explicit allowance, so an O(n)
argument copy is never collapsed to a constant. -/
theorem callNoneMove_words
    (dest : Option Nat) (convArgs names : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (len : convArgs.length = names.length) :
    wordMoveWords (.seq (.move 1 (convArgs.zip names))
      (.call none dest convArgs handler) : WordLangProgHOL (BitVec 64)) =
      convArgs.length + wordMoveWords (.call none dest convArgs handler) := by
  simp only [wordMoveWords, List.length_zip, len, Nat.min_self]

/-- The same accounting in terms of the source argument list length. -/
theorem callNoneMove_words_args (dest : Option Nat) (args convArgs names : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x) :
    wordMoveWords (.seq (.move 1 (convArgs.zip names))
      (.call none dest convArgs handler) : WordLangProgHOL (BitVec 64)) =
      args.length + wordMoveWords (.call none dest convArgs handler) := by
  have len : convArgs.length = names.length := by rw [convEq]; simp
  rw [callNoneMove_words dest convArgs names handler len]
  congr 1
  rw [convEq, namesEq]; simp

/-- The callee entry state of the compiled non-returning call, read off the
source state.  `wsrEq` is the original relation's field decomposition: the
target's post-move state differs from the source state only in locals and
permute, and `callEnv` overwrites the locals, so the entry state is the source
entry state with the target's permutation. -/
theorem callNoneEntry_eq {C F : Type}
    (a : List (WordLocW 64)) (ss : Option Nat)
    (source middle : WordSemStateFiniteExact 64 C F)
    (rel : Flapjack.WordAlloc.wordStateEqRel source middle) :
    callEnv a ss (decClock middle) =
      { callEnv a ss (decClock source) with permute := middle.permute } := by
  conv_lhs => rw [← Flapjack.WordAlloc.wsrEq rel]
  rfl

/-- Word work of the compiled non-returning call given only a transferred body
work at the literal entry states tied by the original `wordStateEqRel`: the
only difference between the two entry states is the stack permutation. -/
theorem bodyWork_call_none_related_body {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat) (calleeBudget : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize =
      some (args1, prog, ss))
    (clock : source.clock ≠ 0)
    (bodyIH : wordPathWork prog
        { callEnv args1 ss (decClock source) with permute := middle.permute } ≤
      wordPathWork prog (callEnv args1 ss (decClock source)) + calleeBudget) :
    wordPathWork (.seq (.move 1 (convArgs.zip names)) (.call none dest convArgs none)) target ≤
      wordPathWork (.call none dest args none) source + (calleeBudget + 2) := by
  have convLen : convArgs.length = names.length := by rw [convEq]; simp
  obtain ⟨values, read, midEq⟩ := callNoneMoveRun names convArgs target middle convLen run
  have relMid : Flapjack.WordAlloc.wordStateEqRel source middle := by
    rw [midEq]
    simpa only [Flapjack.WordAlloc.wordStateEqRel, WordSemStateFiniteExact.setVars] using frame
  have entryEq := callNoneEntry_eq args1 ss source middle relMid
  refine bodyWork_call_none_body dest args ssa next names convArgs source target middle xs
    args1 prog ss calleeBudget frame localsRel namesEq convEq get run bad find clock ?_
  rw [entryEq]
  exact bodyIH

/-- Literal SSA non-returning call output at an arbitrary target option: the
argument move followed by the renamed call. -/
theorem ssaCcTrans_call_none_output
    (dest : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (names convArgs : List Nat) (moveArgs : WordLangProgHOL (BitVec 64))
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (moveEq : moveArgs = .move 1 (convArgs.zip names)) :
    ssaCcTrans (width := 64) (.call none dest args h) ssa next tables =
      (.seq moveArgs (.call none dest convArgs h), ssa, next) := by
  simp only [ssaCcTrans, namesEq, convEq, moveEq]

/-- Actual compiler non-returning call case.  `ssaCcTrans_call_none_output`
supplies the literal inserted move and renamed call, and
`bodyWork_call_none_body` charges the actual move execution plus the callee
BODY transfer at the literal `callEnv` entry states. -/
theorem ssaBody_call_none_executed_le {C F : Type}
    (dest : Option Nat) (args : List Nat) (ssa : Spt Nat) (next : Nat)
    (names convArgs : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat) (calleeBudget : Nat)
    (namesEq : names = args.map (optionLookup ssa))
    (convEq : convArgs = (List.range names.length).map fun x => 2 * x)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (localsRel : ssaLocalsRel next ssa source.locals target.locals)
    (get : getVars args source = some xs)
    (run : evaluate (.move 1 (convArgs.zip names) : WordLangProgHOL (BitVec 64)) target =
      (none, middle))
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) xs) source.code source.stackSize =
      some (args1, prog, ss))
    (clock : source.clock ≠ 0)
    (calleeWork : wordPathWork prog (callEnv args1 ss (decClock middle)) ≤
      wordPathWork prog (callEnv args1 ss (decClock source)) + calleeBudget) :
    wordPathWork (ssaCcTrans (width := 64) (.call none dest args none) ssa next tables).1 target ≤
      wordPathWork (.call none dest args none) source + (calleeBudget + 2) := by
  rw [ssaCcTrans_call_none_output dest args none ssa next tables names convArgs
    (.move 1 (convArgs.zip names)) namesEq convEq rfl]
  dsimp only
  exact bodyWork_call_none_body dest args ssa next names convArgs source target middle xs
    args1 prog ss calleeBudget frame localsRel namesEq convEq get run bad find clock calleeWork

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
#print axioms bodyWork_loopFinal
#print axioms ssaCcTrans_loop_output
#print axioms ssaCcTrans_call_none_output
#print axioms bodyWork_call_none_body
#print axioms bodyWork_call_none_badDest
#print axioms bodyWork_call_none_findCode_none
#print axioms bodyWork_call_none_handler
#print axioms bodyWork_call_none_clock_zero
#print axioms bodyWork_call_none_move_fails
#print axioms ssaBody_call_none_executed_le
#print axioms bodyWork_call_none_related_body
#print axioms callNoneMove_words
#print axioms callNoneMove_words_args
end InitECandidate.Runtime.FineCost

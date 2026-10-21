import InitECandidate.Runtime.SSAAppendReconciliationCost
import InitECandidate.Runtime.SSAQuantitativeAllowanceCore
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticIf
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option pp.structureInstances false

/-- Exact static conditional head plus the larger emitted branch
reconciliation. Only the selected arm executes at runtime. -/
noncomputable def ssaIfLocalPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Nat :=
  match (ssaCcTrans program map next tables).1 with
  | .ite cmp reg imm (.seq a movesA) (.seq b movesB) =>
      price (.ite cmp reg imm (.seq a movesA) (.seq b movesB)) +
        max (ssaReconciliationPrice price movesA) (ssaReconciliationPrice price movesB)
  | _ => 0

/-- Selected branch entry plus its exact reconciliation, with no global
maximum across functions or source sites. -/
noncomputable def ssaIfEntryPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (firstEntry secondEntry : Nat)
    (program : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Nat :=
  match (ssaCcTrans program map next tables).1 with
  | .ite cmp reg imm (.seq a movesA) (.seq b movesB) =>
      price (.ite cmp reg imm (.seq a movesA) (.seq b movesB)) +
        max (ssaReconciliationPrice price movesA + firstEntry)
          (ssaReconciliationPrice price movesB + secondEntry)
  | _ => 0

def ssa_rename_conditional_imm {width : Nat} (ssa : Spt Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg name => .reg (optionLookup ssa name)
  | .imm value => .imm value

/-- Flapjack corollary for the original If proof's two get_var_imm cases.
Success is an internal derived branch fact, never an extra premise of the
public pass case. This has no independent HOL declaration. -/
theorem ssa_get_var_imm_transport {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (ssa : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (immediate : WordRegImm (BitVec width)) (value : WordLocW width)
    (locals : ssaLocalsRel next ssa source.locals target.locals)
    (success : WordSemStateFiniteExact.getVarImm immediate source = some value) :
    WordSemStateFiniteExact.getVarImm (ssa_rename_conditional_imm ssa immediate) target = some value := by
  cases immediate with
  | reg name =>
    exact ssaLocalsRelGetVar next ssa source target name value ⟨locals, success⟩
  | imm word =>
    simpa only [WordSemStateFiniteExact.getVarImm, ssa_rename_conditional_imm] using success

/-- One actual branch witness, followed only on fall-through by the
compiler's reconciliation. All prefix work is computed from emitted leaves. -/
theorem ssa_quantitative_reconciled_branch_entry {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body output moves : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map mapOut finalMap : Spt Nat) (next nextOut nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (n entry : Nat)
    (seqZero : ∀ p q, TP (.seq p q) = 0)
    (compiled : ssaCcTrans body map next tables = (output,mapOut,nextOut))
    (line : lineBound (ssaReconciliationLeaf TP) moves = some n)
    (moveSpec : ∀ (s t : WordSemStateFiniteExact 64 C F),
      ssaLocalsRel nextOut mapOut s.locals t.locals →
      let run := evaluate moves t
      run.1 = none ∧ ssaLocalsRel nextFinal finalMap s.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel t run.2)
    (sim : SSAQuantitativeAllowance SP TP body source target map next tables entry) :
    ∃ permutation,
      SSAQuantitativeOutcome finalMap nextFinal tables
        (evaluate body {source with permute := permutation}) (evaluate (.seq output moves) target)
        (wordExecutionCost (fun p _ => SP p) body {source with permute := permutation} + entry + n)
        (wordExecutionCost (fun p _ => TP p) (.seq output moves) target) := by
  obtain ⟨permutation, post⟩ := sim
  dsimp only at post
  rw [compiled] at post
  refine ⟨permutation, ?_⟩
  exact ssa_append_reconciliation_cost TP seqZero _ target output moves mapOut finalMap nextOut nextFinal tables
    _ n line moveSpec post

theorem ssa_quantitative_reconciled_branch {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body output moves : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (map mapOut finalMap : Spt Nat) (next nextOut nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (n : Nat)
    (seqZero : ∀ p q, TP (.seq p q) = 0)
    (compiled : ssaCcTrans body map next tables = (output,mapOut,nextOut))
    (line : lineBound (ssaReconciliationLeaf TP) moves = some n)
    (moveSpec : ∀ (s t : WordSemStateFiniteExact 64 C F),
      ssaLocalsRel nextOut mapOut s.locals t.locals →
      let run := evaluate moves t
      run.1 = none ∧ ssaLocalsRel nextFinal finalMap s.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel t run.2)
    (sim : SSAQuantitativeSimulation SP TP body source target map next tables) :
    ∃ permutation,
      SSAQuantitativeOutcome finalMap nextFinal tables
        (evaluate body {source with permute := permutation}) (evaluate (.seq output moves) target)
        (wordExecutionCost (fun p _ => SP p) body {source with permute := permutation} + n)
        (wordExecutionCost (fun p _ => TP p) (.seq output moves) target) := by
  have result := ssa_quantitative_reconciled_branch_entry SP TP body output moves source target
    map mapOut finalMap next nextOut nextFinal tables n 0 seqZero compiled line moveSpec
    ((ssa_quantitative_allowance_zero SP TP body source target map next tables).mpr sim)
  simpa only [Nat.add_zero] using result

/-- Full actual conditional SSA case. All six entry invariants derive
branch allocation and reconciliation facts. The two smaller-body quantitative
IHs supply actual branch witnesses; exact emitted reconciliation work is paid
by this source conditional's local price. -/
theorem ssa_quantitative_if_fund_entries {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (operator : Cmp) (left : Nat) (immediate : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstEntry secondEntry : Spt Nat → Nat → Nat)
    (firstIH : ∀ (source target : WordSemStateFiniteExact 64 C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → SSAQuantitativeAllowance SP TP first source target ssa next tables (firstEntry ssa next))
    (secondIH : ∀ (source target : WordSemStateFiniteExact 64 C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → SSAQuantitativeAllowance SP TP second source target ssa next tables (secondEntry ssa next))
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (localPrice : ssaIfEntryPrice TP (firstEntry ssa next)
      (secondEntry ssa (ssaCcTrans first ssa next tables).2.2)
      (.ite operator left immediate first second) ssa next tables ≤
      SP (.ite operator left immediate first second))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.ite operator left immediate first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP (.ite operator left immediate first second) source target ssa next tables := by
  classical
  have vars : decide (left < next) = true ∧ everyVarImmHOL (fun x => decide (x < next)) immediate = true ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      everyVarHOL (fun x => decide (x < next)) second = true := by
    simpa only [everyVarHOL, Bool.and_eq_true, and_assoc] using h.2.2.2.1
  rcases firstCompiled : ssaCcTrans first ssa next tables with ⟨firstOut, mapFirst, nextFirst⟩
  rcases secondCompiled : ssaCcTrans second ssa nextFirst tables with ⟨secondOut, mapSecond, nextSecond⟩
  rcases reconciled : fixInconsistencies (width := 64) (mkPrio firstOut secondOut)
      mapFirst mapSecond nextSecond with ⟨movesFirst, movesSecond, nextFinal, finalMap⟩
  have compiled : ssaCcTrans (.ite operator left immediate first second) ssa next tables =
      (.ite operator (optionLookup ssa left) (ssa_rename_conditional_imm ssa immediate)
        (.seq firstOut movesFirst) (.seq secondOut movesSecond), finalMap, nextFinal) := by
    simp only [ssaCcTrans, firstCompiled, secondCompiled, reconciled, ssa_rename_conditional_imm]
    cases immediate <;> rfl
  obtain ⟨leftWork, rightWork, leftLine, rightLine⟩ :=
    ssa_fix_inconsistencies_line TP (mkPrio firstOut secondOut) mapFirst mapSecond nextSecond
  rw [reconciled] at leftLine rightLine
  dsimp only at leftLine rightLine
  have localBound : TP (.ite operator (optionLookup ssa left) (ssa_rename_conditional_imm ssa immediate)
      (.seq firstOut movesFirst) (.seq secondOut movesSecond)) + max (leftWork + firstEntry ssa next) (rightWork + secondEntry ssa nextFirst) ≤
      SP (.ite operator left immediate first second) := by
    simpa only [ssaIfEntryPrice, compiled, firstCompiled, ssaReconciliationPrice, leftLine, rightLine, Option.getD_some] using localPrice
  have seqZero : ∀ p q, TP (.seq p q) = 0 := by
    intro p q
    have bound := targetPrices (.seq p q)
    change _ ≤ 0 at bound
    omega
  have firstInvariant := ssaCcTransProps first ssa next tables firstOut mapFirst nextFirst
    firstCompiled ⟨h.2.2.2.2.1, h.2.2.1⟩
  have initialMapLater := ssaMapOKMore next ssa nextFirst ⟨h.2.2.2.2.1, firstInvariant.1⟩
  have secondInvariant := ssaCcTransProps second ssa nextFirst tables secondOut mapSecond nextSecond
    secondCompiled ⟨initialMapLater, firstInvariant.2.1⟩
  have readLeft (permutation : Nat → Nat → Nat) :
      WordSemStateFiniteExact.getVar left {source with permute := permutation} =
        WordSemStateFiniteExact.getVar left source := rfl
  have readRight (permutation : Nat → Nat → Nat) :
      WordSemStateFiniteExact.getVarImm immediate {source with permute := permutation} =
        WordSemStateFiniteExact.getVarImm immediate source := by
    cases immediate <;> rfl
  cases sourceLeft : WordSemStateFiniteExact.getVar left source with
  | none =>
    refine ⟨target.permute, ?_⟩
    simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft]
  | some leftValue =>
    cases sourceRight : WordSemStateFiniteExact.getVarImm immediate source with
    | none =>
      refine ⟨target.permute, ?_⟩
      simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight]
    | some rightValue =>
      have targetLeft := ssaLocalsRelGetVar next ssa source target left leftValue ⟨h.2.1, sourceLeft⟩
      have targetRight := ssa_get_var_imm_transport next ssa source target immediate rightValue h.2.1 sourceRight
      cases comparison : wordSemWordCmp operator leftValue rightValue with
      | none =>
        refine ⟨target.permute, ?_⟩
        simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison]
      | some condition =>
        cases condition with
        | false =>
          have secondVars : everyVarHOL (fun x => decide (x < nextFirst)) second = true := by
            apply Flapjack.everyVarMono _ second _
            refine ⟨?_, vars.2.2.2⟩
            intro x bound
            have : x < next := of_decide_eq_true bound
            exact decide_eq_true (Nat.lt_of_lt_of_le this firstInvariant.1)
          have sim := secondIH source target ssa nextFirst tables
            ⟨h.1, ssaLocalsRelMore next ssa source.locals target.locals nextFirst ⟨h.2.1, firstInvariant.1⟩,
              firstInvariant.2.1, secondVars, initialMapLater, h.2.2.2.2.2⟩
          have moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact 64 C F),
              ssaLocalsRel nextSecond mapSecond sourceAfter.locals targetAfter.locals →
              let run := WordSemStateFiniteExact.evaluate movesSecond targetAfter
              run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
                Flapjack.WordAlloc.wordStateEqRel targetAfter run.2 := by
            intro sourceAfter targetAfter locals
            have fixed := fixInconsistenciesCorrectR nextSecond mapFirst mapSecond
              (mkPrio firstOut secondOut) sourceAfter targetAfter
              ⟨secondInvariant.2.1, secondInvariant.2.2⟩
            rw [reconciled] at fixed
            exact fixed locals
          obtain ⟨permutation, branch⟩ := ssa_quantitative_reconciled_branch_entry SP TP second secondOut movesSecond source target
            ssa mapSecond finalMap nextFirst nextSecond nextFinal tables rightWork (secondEntry ssa nextFirst) seqZero secondCompiled rightLine moveSpec sim
          refine ⟨permutation, ?_⟩
          dsimp only
          rw [compiled]
          have sourceRun : evaluate (.ite operator left immediate first second) {source with permute := permutation} =
              evaluate second {source with permute := permutation} := by
            simp only [evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison]
          have targetRun : evaluate (.ite operator (optionLookup ssa left) (ssa_rename_conditional_imm ssa immediate)
              (.seq firstOut movesFirst) (.seq secondOut movesSecond)) target =
              evaluate (.seq secondOut movesSecond) target := by
            simp only [evaluate, targetLeft, targetRight, comparison]
          rw [sourceRun, targetRun]
          rcases branch with error | ⟨same, frame, locals, branchCost⟩
          · exact Or.inl error
          · refine Or.inr ⟨same, frame, locals, ?_⟩
            conv_lhs => rw [wordExecutionCost]
            conv_rhs => rw [wordExecutionCost]
            simp only [readLeft, readRight, sourceLeft, sourceRight, comparison, targetLeft, targetRight]
            have selected := Nat.le_max_right (leftWork + firstEntry ssa next) (rightWork + secondEntry ssa nextFirst)
            omega
        | true =>
          have sim := firstIH source target ssa next tables
            ⟨h.1, h.2.1, h.2.2.1, vars.2.2.1, h.2.2.2.2⟩
          have mapLater := ssaMapOKMore nextFirst mapFirst nextSecond
            ⟨firstInvariant.2.2, secondInvariant.1⟩
          have moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact 64 C F),
              ssaLocalsRel nextFirst mapFirst sourceAfter.locals targetAfter.locals →
              let run := WordSemStateFiniteExact.evaluate movesFirst targetAfter
              run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
                Flapjack.WordAlloc.wordStateEqRel targetAfter run.2 := by
            intro sourceAfter targetAfter locals
            have fixed := fixInconsistenciesCorrectL nextSecond mapFirst mapSecond
              (mkPrio firstOut secondOut) sourceAfter targetAfter ⟨secondInvariant.2.1, mapLater⟩
            rw [reconciled] at fixed
            exact fixed (ssaLocalsRelMore nextFirst mapFirst sourceAfter.locals targetAfter.locals nextSecond
              ⟨locals, secondInvariant.1⟩)
          obtain ⟨permutation, branch⟩ := ssa_quantitative_reconciled_branch_entry SP TP first firstOut movesFirst source target
            ssa mapFirst finalMap next nextFirst nextFinal tables leftWork (firstEntry ssa next) seqZero firstCompiled leftLine moveSpec sim
          refine ⟨permutation, ?_⟩
          dsimp only
          rw [compiled]
          have sourceRun : evaluate (.ite operator left immediate first second) {source with permute := permutation} =
              evaluate first {source with permute := permutation} := by
            simp only [evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison]
          have targetRun : evaluate (.ite operator (optionLookup ssa left) (ssa_rename_conditional_imm ssa immediate)
              (.seq firstOut movesFirst) (.seq secondOut movesSecond)) target =
              evaluate (.seq firstOut movesFirst) target := by
            simp only [evaluate, targetLeft, targetRight, comparison]
          rw [sourceRun, targetRun]
          rcases branch with error | ⟨same, frame, locals, branchCost⟩
          · exact Or.inl error
          · refine Or.inr ⟨same, frame, locals, ?_⟩
            conv_lhs => rw [wordExecutionCost]
            conv_rhs => rw [wordExecutionCost]
            simp only [readLeft, readRight, sourceLeft, sourceRight, comparison, targetLeft, targetRight]
            have selected := Nat.le_max_left (leftWork + firstEntry ssa next) (rightWork + secondEntry ssa nextFirst)
            omega


/-- Zero-entry specialization preserves the original conditional API. -/
theorem ssa_quantitative_if {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (operator : Cmp) (left : Nat) (immediate : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstIH : ∀ (source target : WordSemStateFiniteExact 64 C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → SSAQuantitativeSimulation SP TP first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact 64 C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → SSAQuantitativeSimulation SP TP second source target ssa next tables)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (localPrice : ssaIfLocalPrice TP (.ite operator left immediate first second) ssa next tables ≤
      SP (.ite operator left immediate first second))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.ite operator left immediate first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP (.ite operator left immediate first second) source target ssa next tables := by
  apply ssa_quantitative_if_fund_entries SP TP operator left immediate first second source target
    ssa next tables (fun _ _ => 0) (fun _ _ => 0)
  · intro s t m n ts premises
    exact (ssa_quantitative_allowance_zero SP TP first s t m n ts).mpr (firstIH s t m n ts premises)
  · intro s t m n ts premises
    exact (ssa_quantitative_allowance_zero SP TP second s t m n ts).mpr (secondIH s t m n ts premises)
  · exact targetPrices
  · simpa only [ssaIfEntryPrice,ssaIfLocalPrice,Nat.add_zero] using localPrice
  · exact h

#print axioms ssa_quantitative_reconciled_branch_entry
#print axioms ssa_quantitative_if_fund_entries
#print axioms ssa_quantitative_reconciled_branch
#print axioms ssa_quantitative_if
end InitECandidate.Runtime.FineCost

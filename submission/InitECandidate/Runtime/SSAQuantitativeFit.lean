import InitECandidate.Runtime.SSAQuantitativeAtomic
import InitECandidate.Runtime.SSAQuantitativeAllowance
import InitECandidate.Runtime.SSAQuantitativeIf
import InitECandidate.Runtime.SSAQuantitativeMustTerminate
import InitECandidate.Runtime.SSAQuantitativeLoopEntry
import InitECandidate.Runtime.SSAQuantitativeReturningSome
import InitECandidate.Runtime.SSAQuantitativeTail
import Flapjack.Pancake.WordConvs.ProgramMonotonicity

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 10000000
set_option pp.structureInstances false

/-- Static local-price certificates at the contexts the actual compiler
visits, including returning calls with both continuations.
No execution, target run, semantic simulation or whole-run bound is a field. -/
noncomputable def ssaCostFits (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Prop :=
  match p with
  | .seq first second =>
    let firstC := ssaCcTrans first map next tables
    let secondC := ssaCcTrans second firstC.2.1 firstC.2.2 tables
    TP (.seq firstC.1 secondC.1) + ssaRootEntryAllowance TP first map next +
        ssaRootEntryAllowance TP second firstC.2.1 firstC.2.2 ≤ SP p ∧
      ssaCostFits SP TP first map next tables ∧
      ssaCostFits SP TP second firstC.2.1 firstC.2.2 tables
  | .ite _ _ _ first second =>
    let secondNext := (ssaCcTrans first map next tables).2.2
    ssaIfEntryPrice TP (ssaRootEntryAllowance TP first map next)
        (ssaRootEntryAllowance TP second map secondNext) p map next tables ≤ SP p ∧
      ssaCostFits SP TP first map next tables ∧
      ssaCostFits SP TP second map secondNext tables
  | .mustTerminate body =>
    TP (ssaCcTrans p map next tables).1 + ssaRootEntryAllowance TP body map next ≤ SP p ∧
      ssaCostFits SP TP body map next tables
  | .loop names body exits =>
    let setup := loopSetup (width := 64) names exits map next
    let ctx := ssaLoopCostContext SP TP names exits body map next tables
    let bodyMap := sptInter setup.2.1 names
    TP ctx.targetLoop + TP ctx.moves + ssaRootEntryAllowance TP body bodyMap setup.2.2 ≤ SP p ∧
      ssaCostFits SP TP body bodyMap setup.2.2 ((setup.2.1,names,exits)::tables)
  | .call none dest args none => ssaTailLocalPrice TP dest args map ≤ SP p
  | .call (some (_,_,body,_,_)) _ _ none =>
    let binding := ssaReturningBodyContext p map next
    ssaReturningEntryPrice TP (ssaRootEntryAllowance TP body) p map next tables ≤ SP p ∧
      ssaCostFits SP TP body binding.1 binding.2 tables
  | .call (some (_,_,body,_,_)) _ _ (some (_,handlerBody,_,_)) =>
    let contexts := ssaReturningSomeContexts p map next tables
    ssaReturningSomeEntryPrice TP (ssaRootEntryAllowance TP body) (ssaRootEntryAllowance TP handlerBody)
        p map next tables ≤ SP p ∧
      ssaCostFits SP TP body contexts.1.1 contexts.1.2 tables ∧
      ssaCostFits SP TP handlerBody contexts.2.1 contexts.2.2 tables
  | .call none _ _ (some _) => False
  | _ => ssaAtomicPrice TP (ssaCcTrans p map next tables).1 ≤ SP p
termination_by sizeOf p

/-- Structural SSA work transfer from static certificates. Only a root loop
retains a one-time setup allowance; every other constructor funds child entry
work locally. Semantics, frame, result locals and cost share one permutation.
This is a one-program theorem with the original unchanged callee code table. -/
theorem ssa_quantitative_of_fit {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (optimizer : ∀ p (s : WordSemStateFiniteExact 64 C F), TP p ≤ wordOptimizerLocalPrice p s)
    (sourcePrices : ∀ p, TP p ≤ SP p)
    (p : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (fit : ssaCostFits SP TP p map next tables)
    (source target : WordSemStateFiniteExact 64 C F)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) p = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    SSAQuantitativeAllowance SP TP p source target map next tables (ssaRootEntryAllowance TP p map next) := by
  have seqZero : ∀ a b, TP (.seq a b) = 0 := by
    intro a b
    have bound := optimizer (.seq a b) target
    change _ ≤ 0 at bound
    omega
  cases p with
  | seq first second =>
    simp only [ssaCostFits] at fit
    rcases firstCompiled : ssaCcTrans first map next tables with ⟨firstOut,mapFirst,nextFirst⟩
    rcases secondCompiled : ssaCcTrans second mapFirst nextFirst tables with ⟨secondOut,mapSecond,nextSecond⟩
    rw [firstCompiled,secondCompiled] at fit
    dsimp only at fit
    have vars : everyVarHOL (fun x => decide (x < next)) first = true ∧
        everyVarHOL (fun x => decide (x < next)) second = true := by
      simpa only [everyVarHOL,Bool.and_eq_true] using h.2.2.2.1
    have invariant := ssaCcTransProps first map next tables firstOut mapFirst nextFirst
      firstCompiled ⟨h.2.2.2.2.1,h.2.2.1⟩
    apply (ssa_quantitative_allowance_zero SP TP (.seq first second) source target map next tables).mpr
    apply ssa_quantitative_seq_fund_entries SP TP first second firstOut secondOut source target
      map mapFirst mapSecond next nextFirst nextSecond tables firstCompiled secondCompiled
      (ssaRootEntryAllowance TP first map next) (ssaRootEntryAllowance TP second mapFirst nextFirst) fit.1
    · exact ssa_quantitative_of_fit SP TP optimizer sourcePrices first map next tables fit.2.1 source target
        ⟨h.1,h.2.1,h.2.2.1,vars.1,h.2.2.2.2⟩
    · intro s t frame locals
      apply ssa_quantitative_of_fit SP TP optimizer sourcePrices second mapFirst nextFirst tables fit.2.2 s t
      refine ⟨frame,locals,invariant.2.1,?_,invariant.2.2,h.2.2.2.2.2⟩
      exact Flapjack.everyVarMono _ second _
        ⟨fun key bound => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true bound) invariant.1),vars.2⟩
  | ite operator left immediate first second =>
    simp only [ssaCostFits] at fit
    apply (ssa_quantitative_allowance_zero SP TP (.ite operator left immediate first second)
      source target map next tables).mpr
    apply ssa_quantitative_if_fund_entries SP TP operator left immediate first second source target map next tables
      (ssaRootEntryAllowance TP first) (ssaRootEntryAllowance TP second)
    · intro s t premises
      exact ssa_quantitative_of_fit SP TP optimizer sourcePrices first map next tables fit.2.1 s t premises
    · intro s t premises
      exact ssa_quantitative_of_fit SP TP optimizer sourcePrices second map
        (ssaCcTrans first map next tables).2.2 tables fit.2.2 s t premises
    · exact fun q => optimizer q target
    · exact fit.1
    · exact h
  | mustTerminate body =>
    simp only [ssaCostFits] at fit
    apply (ssa_quantitative_allowance_zero SP TP (.mustTerminate body) source target map next tables).mpr
    apply ssa_quantitative_mustTerminate_fund_entry SP TP body source target map next tables
      (ssaRootEntryAllowance TP body map next)
    · intro s t premises
      exact ssa_quantitative_of_fit SP TP optimizer sourcePrices body map next tables fit.2 s t premises
    · exact h
    · exact fit.1
  | loop names body exits =>
    simp only [ssaCostFits] at fit
    apply ssa_quantitative_loop_with_setup_fund_body SP TP names exits body source target map next tables
      (ssaRootEntryAllowance TP body) seqZero
    · exact fit.1
    · intro s t premises
      let setup := loopSetup (width := 64) names exits map next
      exact ssa_quantitative_of_fit SP TP optimizer sourcePrices body (sptInter setup.2.1 names) setup.2.2
        ((setup.2.1,names,exits)::tables) fit.2 s t premises
    · exact h
  | call returns dest args handler =>
    cases handler with
    | some handlerPayload =>
      obtain ⟨exceptionVar,handlerBody,handlerL1,handlerL2,handlerShape⟩ :
          ∃ (exceptionVar : Nat) (handlerBody : WordLangProgHOL (BitVec 64)) (handlerL1 handlerL2 : Nat),
            handlerPayload = (exceptionVar,handlerBody,handlerL1,handlerL2) := by
        rcases handlerPayload with ⟨exceptionVar,handlerBody,handlerL1,handlerL2⟩
        exact ⟨exceptionVar,handlerBody,handlerL1,handlerL2,rfl⟩
      rw [handlerShape] at fit h ⊢
      cases returns with
      | none => simp only [ssaCostFits] at fit
      | some payload =>
        obtain ⟨returns,firstNames,secondNames,body,l1,l2,payloadShape⟩ :
            ∃ (returns : List Nat) (firstNames secondNames : Spt Unit)
              (body : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat),
              payload = (returns,(firstNames,secondNames),body,l1,l2) := by
          rcases payload with ⟨returns,⟨firstNames,secondNames⟩,body,l1,l2⟩
          exact ⟨returns,firstNames,secondNames,body,l1,l2,rfl⟩
        rw [payloadShape] at fit h ⊢
        simp only [ssaCostFits] at fit
        apply (ssa_quantitative_allowance_zero SP TP
          (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args
            (some (exceptionVar,handlerBody,handlerL1,handlerL2))) source target map next tables).mpr
        apply ssa_quantitative_returning_some_fund_entry SP TP
          (ssaRootEntryAllowance TP body) (ssaRootEntryAllowance TP handlerBody)
          source target map next returns firstNames secondNames body handlerBody l1 l2
          exceptionVar handlerL1 handlerL2 dest args tables
        · dsimp only
          intro s t premises
          let contexts := ssaReturningSomeContexts
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args
              (some (exceptionVar,handlerBody,handlerL1,handlerL2))) map next tables
          exact ssa_quantitative_of_fit SP TP optimizer sourcePrices body contexts.1.1 contexts.1.2
            tables fit.2.1 s t premises
        · dsimp only
          intro s t premises
          let contexts := ssaReturningSomeContexts
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args
              (some (exceptionVar,handlerBody,handlerL1,handlerL2))) map next tables
          exact ssa_quantitative_of_fit SP TP optimizer sourcePrices handlerBody contexts.2.1 contexts.2.2
            tables fit.2.2 s t premises
        · exact sourcePrices
        · exact fun q => optimizer q target
        · exact fit.1
        · exact h
    | none =>
      cases returns with
      | none =>
        simp only [ssaCostFits] at fit
        apply (ssa_quantitative_allowance_zero SP TP (.call none dest args none) source target map next tables).mpr
        exact ssa_quantitative_tail SP TP source target map next dest args tables h sourcePrices fit
      | some payload =>
        obtain ⟨returns,firstNames,secondNames,body,l1,l2,payloadShape⟩ :
            ∃ (returns : List Nat) (firstNames secondNames : Spt Unit)
              (body : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat),
              payload = (returns,(firstNames,secondNames),body,l1,l2) := by
          rcases payload with ⟨returns,⟨firstNames,secondNames⟩,body,l1,l2⟩
          exact ⟨returns,firstNames,secondNames,body,l1,l2,rfl⟩
        rw [payloadShape] at fit h ⊢
        simp only [ssaCostFits] at fit
        apply (ssa_quantitative_allowance_zero SP TP
          (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) source target map next tables).mpr
        apply ssa_quantitative_returning_none_fund_entry SP TP (ssaRootEntryAllowance TP body)
          source target map next returns firstNames secondNames body l1 l2 dest args tables
        · intro s t premises
          let binding := ssaReturningBodyContext
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) map next
          exact ssa_quantitative_of_fit SP TP optimizer sourcePrices body binding.1 binding.2 tables fit.2 s t premises
        · exact sourcePrices
        · exact fun q => optimizer q target
        · exact fit.1
        · exact h
  | _ =>
    simp only [ssaCostFits] at fit
    apply (ssa_quantitative_allowance_zero SP TP _ source target map next tables).mpr
    exact ssa_quantitative_atomic SP TP _ source target map next tables rfl seqZero fit h
termination_by sizeOf p
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

#print axioms ssaCostFits
#print axioms ssa_quantitative_of_fit
end InitECandidate.Runtime.FineCost

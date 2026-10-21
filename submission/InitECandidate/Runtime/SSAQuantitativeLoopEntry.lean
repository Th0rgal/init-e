import InitECandidate.Runtime.SSALoopRecursiveOutcome
import InitECandidate.Runtime.SSALoopSetupExactCost
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- The context comes from the actual setup and body compilation, including
its refreshed map, output counter and concrete back-edge syntax. -/
def ssaLoopCostContext (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) : SSALoopCostContext :=
  let setup := loopSetup (width := 64) names exits map next
  let compiled := ssaCcTrans body (sptInter setup.2.1 names) setup.2.2 ((setup.2.1,names,exits)::tables)
  { SP,TP,names,exits,refreshed := setup.2.1,mapOut := compiled.2.1,nextOut := compiled.2.2,
    body,output := compiled.1,tables }

/-- Full actual SSA loop compilation with its setup paid ONCE, as an explicit
entry allowance. The repeated loop theorem does not include setup in its
head price. A whole-program composition must fund this entry allowance. -/
theorem ssa_quantitative_loop_with_setup {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (headCost : let ctx := ssaLoopCostContext SP TP names exits body map next tables
      TP ctx.targetLoop + TP ctx.moves ≤ SP ctx.sourceLoop)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F) (m : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na m st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na m ∧ ltOK lt → SSAQuantitativeSimulation SP TP body st ct m na lt)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) (.loop names body exits) = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    ∃ permutation,
      let compiled := ssaCcTrans (.loop names body exits) map next tables
      let sourceState := {source with permute := permutation}
      let sourceRun := evaluate (.loop names body exits) sourceState
      let targetRun := evaluate compiled.1 target
      sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        SSAResultLocals compiled.2.2 compiled.2.1 tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
        wordExecutionCost (fun p _ => TP p) compiled.1 target ≤
          wordExecutionCost (fun p _ => SP p) (.loop names body exits) sourceState +
            ssaReconciliationPrice TP (loopSetup (width := 64) names exits map next).1 := by
  classical
  obtain ⟨frame,locals,allocated,vars,valid,tableValid⟩ := premises
  have bounds : ((∀ key ∈ (sptToAList names).map Prod.fst, key < next) ∧
      everyVarHOL (fun key => decide (key < next)) body = true) ∧
      (∀ key ∈ (sptToAList exits).map Prod.fst, key < next) := by
    simpa only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using vars
  rcases setup : loopSetup (width := 64) names exits map next with ⟨setupProg,refreshed,nextRefreshed⟩
  obtain ⟨after,setupRun,afterFrame,afterLocals,afterStrong,increase,afterAllocated,afterValid,
    domain,entryInjection,exitInjection,images,setupCost⟩ :=
    loopSetupCorrect_exact_cost TP seqZero source target map next names exits setupProg refreshed nextRefreshed
      frame locals valid allocated setup
  have namesMapped : ∀ key, sptDomain names key → sptDomain refreshed key := by
    intro key member
    rw [domain,sptDomain_sptUnion]
    exact Or.inr (Or.inl member)
  have exitsMapped : ∀ key, sptDomain exits key → sptDomain refreshed key := by
    intro key member
    rw [domain,sptDomain_sptUnion]
    exact Or.inr (Or.inr member)
  have bodyVars : everyVarHOL (fun key => decide (key < nextRefreshed)) body = true :=
    Flapjack.everyVarMono _ body _ ⟨fun key bound => by
      simp only [decide_eq_true_eq] at bound ⊢
      exact Nat.lt_of_lt_of_le bound increase, bounds.1.2⟩
  rcases compiledBody : ssaCcTrans body (sptInter refreshed names) nextRefreshed
      ((refreshed,names,exits)::tables) with ⟨output,mapOut,nextOut⟩
  let ctx : SSALoopCostContext := { SP,TP,names,exits,refreshed,mapOut,nextOut,body,output,tables }
  have ctxHead : TP ctx.targetLoop + TP ctx.moves ≤ SP ctx.sourceLoop := by
    simpa only [ssaLoopCostContext,setup,compiledBody] using headCost
  have compiled : ssaCcTrans (.loop names body exits) map next tables =
      (.seq setupProg ctx.targetLoop,sptInter refreshed exits,nextOut) := by
    simp only [ssaCcTrans,setup,compiledBody]
    dsimp only [ctx,SSALoopCostContext.targetLoop,SSALoopCostContext.finalBody,
      SSALoopCostContext.moves,SSALoopCostContext.targetNames,SSALoopCostContext.targetExits]
    cases ssaReconcile (width := 64) mapOut refreshed names <;> rfl
  rcases targetRun : evaluate ctx.targetLoop after with ⟨targetResult,targetFinal⟩
  have inner := ssa_loop_quantitative_context ctx nextRefreshed compiledBody afterValid afterAllocated
    bodyVars entryInjection exitInjection namesMapped exitsMapped
    (fun key member => Nat.lt_of_lt_of_le
      (bounds.1.1 key ((sptMemMapFstToAList names key).mpr member)) increase)
    (fun key member => Nat.lt_of_lt_of_le
      (bounds.2 key ((sptMemMapFstToAList exits key).mpr member)) increase)
    tableValid seqZero ctxHead bodyIH source after afterFrame afterStrong targetResult targetFinal targetRun
  obtain ⟨permutation,post⟩ := inner
  refine ⟨permutation,?_⟩
  dsimp only
  rw [compiled]
  have targetWhole : evaluate (.seq setupProg ctx.targetLoop) target = (targetResult,targetFinal) := by
    exact (evaluateSeqCollapse setupProg ctx.targetLoop target after setupRun).trans targetRun
  rw [targetWhole]
  dsimp only at post ⊢
  rcases sourceRun : evaluate ctx.sourceLoop {source with permute := permutation} with ⟨result,sourceFinal⟩
  rw [sourceRun] at post
  dsimp only
  rcases post with error | ⟨same,finalFrame,finalLocals,innerCost⟩
  · exact Or.inl error
  · refine Or.inr ⟨same,finalFrame,finalLocals,?_⟩
    rw [wordExecutionCost_seq,setupRun,seqZero,Nat.zero_add]
    dsimp only
    calc
      _ ≤ ssaReconciliationPrice TP setupProg +
          wordExecutionCost (fun p _ => SP p) (.loop names body exits) {source with permute := permutation} :=
        Nat.add_le_add setupCost innerCost
      _ = _ := Nat.add_comm _ _

#print axioms ssa_quantitative_loop_with_setup
end InitECandidate.Runtime.FineCost

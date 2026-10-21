import InitECandidate.Runtime.SSAQuantitativeFit
import Flapjack.Compiler.Backend.WordAlloc.Proofs.FullSSACorrect
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- One actual function invocation pays its argument-renaming prologue and,
only for a root loop, the single SSA setup allowance. -/
noncomputable def fullSSAEntryPrice (TP : WordLangProgHOL (BitVec 64) → Nat)
    (count : Nat) (program : WordLangProgHOL (BitVec 64)) : Nat :=
  let setup := setupSSA (outputWidth := 64) count (limitVar program) program
  TP setup.1 + ssaRootEntryAllowance TP program setup.2.1 setup.2.2

/-- Quantitative full function SSA, including the actual setupSSA prologue.
The only initial-state premise is the argument convention; all body simulation
invariants are derived. Static fit certificates contain no target runs. As in
the local theorem, callee code is unchanged at this stage. -/
theorem fullSSA_quantitative_of_fit {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (optimizer : ∀ p (s : WordSemStateFiniteExact 64 C F), TP p ≤ wordOptimizerLocalPrice p s)
    (sourcePrices : ∀ p, TP p ≤ SP p)
    (program : WordLangProgHOL (BitVec 64)) (count : Nat)
    (fit : let setup := setupSSA (outputWidth := 64) count (limitVar program) program
      ssaCostFits SP TP program setup.2.1 setup.2.2 [])
    (state : WordSemStateFiniteExact 64 C F)
    (domain : sptDomain state.locals = (fun key => key ∈ evenList count)) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {state with permute := permutation}
      let sourceRun := evaluate program sourceState
      let targetRun := evaluate (fullSsaCcTrans count program) state
      sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        (match sourceRun.1 with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => sourceRun.2.locals = targetRun.2.locals) ∧
        wordExecutionCost (fun p _ => TP p) (fullSsaCcTrans count program) state ≤
          wordExecutionCost (fun p _ => SP p) program sourceState + fullSSAEntryPrice TP count program := by
  obtain ⟨allocated,bounded⟩ := limitVarProps program (limitVar program) rfl
  rcases produced : setupSSA (outputWidth := 64) count (limitVar program) program with ⟨move,map,next⟩
  rcases run : evaluate move state with ⟨result,target⟩
  have setup := setupSSAProps (limitVar program) count state program ⟨allocated,domain⟩
  rw [produced] at setup
  dsimp only at setup
  rw [run] at setup
  obtain ⟨rfl,frame,valid,related,nextAllocated,increase⟩ := setup
  have vars : everyVarHOL (fun key => decide (key < next)) program = true := by
    apply Flapjack.everyVarMono _ program _
    refine ⟨?_,bounded⟩
    intro key bound
    simp only [decide_eq_true_eq] at bound ⊢
    omega
  dsimp only at fit
  rw [produced] at fit
  dsimp only at fit
  obtain ⟨permutation,post⟩ := ssa_quantitative_of_fit SP TP optimizer sourcePrices program map next []
    fit state target ⟨frame,related,nextAllocated,vars,valid,by simp [ltOK]⟩
  have seqZero : ∀ a b, TP (.seq a b) = 0 := by
    intro a b
    have bound := optimizer (.seq a b) state
    change _ ≤ 0 at bound
    omega
  have moveAtomic : wordCostAtomic move = true := by
    have shape := congrArg Prod.fst produced
    simp only [setupSSA] at shape
    rw [←shape]
    rfl
  have executed : evaluate (fullSsaCcTrans count program) state =
      evaluate (ssaCcTrans program map next []).1 target := by
    simp only [fullSsaCcTrans,produced]
    exact evaluateSeqCollapse _ _ state target run
  have costPrefix : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
      (fullSsaCcTrans count program) state =
      TP move + wordExecutionCost (fun p _ => TP p) (ssaCcTrans program map next []).1 target := by
    simp only [fullSsaCcTrans,produced]
    rw [wordExecutionCost_seq,run]
    simp only [seqZero,Nat.zero_add]
    rw [wordExecutionCost_atomic _ move _ moveAtomic]
  refine ⟨permutation,?_⟩
  dsimp only at post ⊢
  rw [executed]
  rcases post with error | ⟨same,postFrame,locals,cost⟩
  · exact Or.inl error
  · right
    refine ⟨same,postFrame,?_,?_⟩
    · cases resultEq : (evaluate program {state with permute := permutation}).1 with
      | none => trivial
      | some result =>
        cases result <;> simp only [resultEq,SSAResultLocals] at locals ⊢
        all_goals first | trivial | exact locals
    · rw [costPrefix]
      simp only [fullSSAEntryPrice,produced]
      omega

#print axioms fullSSAEntryPrice
#print axioms fullSSA_quantitative_of_fit
end InitECandidate.Runtime.FineCost

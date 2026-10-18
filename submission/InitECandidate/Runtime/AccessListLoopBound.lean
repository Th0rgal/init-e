import InitECandidate.Runtime.AccessListLoopWitness
import InitECandidate.Runtime.AccessListOuterStepControl
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessLoop := accessAt 4

theorem source_access_loop : accessLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) accessStep := by
  simp only [accessLoop,accessStep,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual access-list loop has an input-dependent clock bound,
including memory failures and exceptions from record validation. -/
theorem evaluate_access_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state accessLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (accessStepCost inputLength.toNat inputLength.toNat + 1) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : AccessLoopWitness post array count records input inputLength scratch frame ceiling,
        next.index = count) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (AccessLoopWitness current array count records input inputLength scratch frame ceiling)
  let cost := accessStepCost inputLength.toNat inputLength.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : AccessLoopWitness current array count records input inputLength scratch frame ceiling,
      accessRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [accessRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) =
      some (.val (.word (if accessRank count current = 0 then 0 else 1))) := by
    rintro current ⟨witness⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : accessRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : accessRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness⟩; exact ⟨witness.decClock⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      accessRank count (decClockHOLFinite current) = accessRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < accessRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current accessStep = (none,post) ∧ invariant post ∧
          accessRank count post < accessRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current accessStep = (some result,post))) := by
    rintro current ⟨witness⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    have heapBeforeFrame : witness.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by
      have reserve := witness.reserve
      omega
    have parserSpace : witness.heap.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by
      have reserve := witness.reserve
      omega
    have bounded := evaluate_access_step_input_bounded current witness.index array count input inputLength scratch frame witness.heap
      ceiling inputLimit witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
      witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
      witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap heapBeforeFrame parserSpace ticks
    have control := evaluate_access_outer_step_control current
    cases run : evaluateHOLFiniteState current accessStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := access_loop_witness_step current post array count records input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit inputBeforeFrame arrayBeforeFrame arrayBeforeRecords ticks run
        exact Or.inl ⟨rfl,⟨next⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) accessStep
    invariant (accessRank count) cost guard enter entryRank step state ⟨valid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_access_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨next⟩,zero⟩ := done normal
    refine ⟨next,BitVec.eq_of_toNat_eq ?_⟩
    rw [rankEq post next] at zero
    have bounded := next.indexBound
    omega

#print axioms evaluate_access_loop_bounded
end InitECandidate.Runtime

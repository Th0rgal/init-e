import InitECandidate.Runtime.AuthorizationsLoopIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopHeapBound
import InitECandidate.Runtime.AuthorizationsStepInputHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsStepInputHeapBound
import InitECandidate.Runtime.AuthorizationsLoopHeapWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual authorization loop has an input-dependent clock bound,
including memory failures and exceptions from record validation. -/
theorem evaluate_authorizations_loop_independent_outer_prefix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state authorizationLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : AuthorizationsHeapLoopWitness post array count records input inputLength scratch frame ceiling,
        next.index = count ∧ RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (AuthorizationsHeapLoopWitness current array count records input inputLength scratch frame ceiling) ∧
      RlpSliceInputPrefix current watchedArray watchedInput watchedLength watchedCount.toNat
  let cost := authorizationStepCost inputLength.toNat inputLength.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : AuthorizationsHeapLoopWitness current array count records input inputLength scratch frame ceiling,
      authorizationRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [authorizationRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) =
      some (.val (.word (if authorizationRank count current = 0 then 0 else 1))) := by
    rintro current ⟨⟨witness⟩,watched⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : authorizationRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : authorizationRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨⟨witness⟩,watched⟩
    refine ⟨⟨witness.decClock⟩,?_⟩
    intro slot inside
    obtain ⟨p,n,item⟩ := watched slot inside
    exact ⟨p,n,item.after_frame current _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      authorizationRank count (decClockHOLFinite current) = authorizationRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < authorizationRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current authorizationStep = (none,post) ∧ invariant post ∧
          authorizationRank count post < authorizationRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current authorizationStep = (some result,post))) := by
    rintro current ⟨⟨witness⟩,watched⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    let record := records + witness.index * 120#64
    have recordNat : record.toNat = records.toNat + witness.index.toNat * 120 := by
      have product : (witness.index * 120#64).toNat = witness.index.toNat * 120 := by
        apply BitVec.toNat_mul_of_lt
        have b := witness.recordsBeforeHeap
        have h := witness.heapBound
        change witness.index.toNat * 120 < 2^64
        omega
      dsimp only [record]
      rw [BitVec.toNat_add_of_lt (by rw [product]; have b := witness.recordsBeforeHeap; have h := witness.heapBound; omega),product]
    have recordBeforeHeap : record.toNat + 120 ≤ witness.heap.toNat := by
      rw [recordNat]
      have b := witness.recordsBeforeHeap
      omega
    have bounded := evaluate_authorization_step_input_heap_bounded current record records witness.index array count input inputLength scratch frame witness.heap
      ceiling inputLimit rfl witness.recordsLocal witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
      witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
      witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap witness.heapAbove recordBeforeHeap
      (by have h := witness.heapBound; omega) ticks
    have control := evaluate_authorization_step_control current
    cases run : evaluateHOLFiniteState current authorizationStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := authorizations_heap_loop_witness_step current post array count records input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit inputBeforeFrame arrayFits arrayAbove arrayBeforeRecords ticks run
        have retained := authorization_step_input_heap_independent_outer_prefix current post record records witness.index array count input inputLength scratch frame witness.heap
          ceiling inputLimit rfl witness.recordsLocal witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
          witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
          witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap witness.heapAbove recordBeforeHeap
          (by have h := witness.heapBound; omega) ticks watchedArray watchedCount watchedInput watchedLength watched watchedFits watchedAbove
          (by rw [recordNat]; omega) run
        exact Or.inl ⟨rfl,⟨⟨next⟩,retained⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) authorizationStep
    invariant (authorizationRank count) cost guard enter entryRank step state ⟨⟨valid⟩,watchedValid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_authorization_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨⟨next⟩,retained⟩,zero⟩ := done normal
    refine ⟨next,BitVec.eq_of_toNat_eq ?_,retained⟩
    rw [rankEq post next] at zero
    have bounded := next.indexBound
    omega

#print axioms evaluate_authorizations_loop_independent_outer_prefix_heap_bounded
end InitECandidate.Runtime

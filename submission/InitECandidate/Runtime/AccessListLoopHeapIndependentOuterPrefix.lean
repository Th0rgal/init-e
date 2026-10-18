import InitECandidate.Runtime.AccessListStepInputHeapBound
import InitECandidate.Runtime.AccessListLoopBound
import InitECandidate.Runtime.AccessListStepInputHeapIndependentOuterPrefix
import InitECandidate.Runtime.AccessListHeapLoopWitness
import InitECandidate.Runtime.AccessListOuterStepControl
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual access-list loop has an input-dependent clock bound,
including memory failures and exceptions from record validation. -/
theorem evaluate_access_loop_heap_independent_outer_prefix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state accessLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (accessStepCost inputLength.toNat inputLength.toNat + 1) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : AccessHeapLoopWitness post array count records input inputLength scratch frame ceiling,
        next.index = count ∧ RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (AccessHeapLoopWitness current array count records input inputLength scratch frame ceiling) ∧
      RlpSliceInputPrefix current watchedArray watchedInput watchedLength watchedCount.toNat
  let cost := accessStepCost inputLength.toNat inputLength.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : AccessHeapLoopWitness current array count records input inputLength scratch frame ceiling,
      accessRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [accessRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) =
      some (.val (.word (if accessRank count current = 0 then 0 else 1))) := by
    rintro current ⟨⟨witness⟩,kept⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : accessRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : accessRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨⟨witness⟩,kept⟩; exact ⟨⟨witness.decClock⟩,kept.dec_clock current watchedArray watchedInput watchedLength _⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      accessRank count (decClockHOLFinite current) = accessRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < accessRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current accessStep = (none,post) ∧ invariant post ∧
          accessRank count post < accessRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current accessStep = (some result,post))) := by
    rintro current ⟨⟨witness⟩,kept⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    have heapAbove : ceiling ≤ witness.heap.toNat := by
      have recordsEnd := witness.recordsBeforeHeap
      omega
    have bounded := evaluate_access_step_input_heap_bounded current witness.index array count input inputLength scratch frame witness.heap
      ceiling inputLimit witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
      witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
      witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap heapAbove ticks
    have control := evaluate_access_outer_step_control current
    cases run : evaluateHOLFiniteState current accessStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := access_heap_loop_witness_step current post array count records input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit inputBeforeFrame arrayAbove arrayBeforeRecords ticks run
        have recordNat : (records + witness.index * 24#64).toNat = records.toNat + witness.index.toNat * 24 := by
          have bound := witness.recordsBeforeHeap
          have heapBound := witness.heapBound
          have product : (witness.index * 24#64).toNat = witness.index.toNat * 24 := by
            apply BitVec.toNat_mul_of_lt
            change witness.index.toNat * 24 < 2^64
            omega
          rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
        have retained := access_step_input_heap_independent_outer_prefix current post witness.index array count input inputLength scratch frame witness.heap ceiling inputLimit
          witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound witness.scratchGlobal witness.frameGlobal witness.code
          orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal witness.heapBound countLimit witness.heapArena inputBeforeFrame
          witness.inputBeforeHeap ticks watchedArray watchedCount watchedInput watchedLength kept records witness.recordsLocal watchedAbove
          (by have h := witness.recordsBeforeHeap; omega) (by rw [recordNat]; omega)
          (by rw [recordNat]; have h := witness.recordsBeforeHeap; have limit := witness.heapBound; omega) run
        exact Or.inl ⟨rfl,⟨⟨next⟩,retained⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) accessStep
    invariant (accessRank count) cost guard enter entryRank step state ⟨⟨valid⟩,watchedValid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_access_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨⟨next⟩,retained⟩,zero⟩ := done normal
    refine ⟨next,BitVec.eq_of_toNat_eq ?_,retained⟩
    rw [rankEq post next] at zero
    have bounded := next.indexBound
    omega

#print axioms evaluate_access_loop_heap_independent_outer_prefix_bounded
end InitECandidate.Runtime

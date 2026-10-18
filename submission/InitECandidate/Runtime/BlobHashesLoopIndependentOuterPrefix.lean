import InitECandidate.Runtime.BlobHashesLoopBound
import InitECandidate.Runtime.BlobHashesStepIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Complete original blob traversal has an explicit input-dependent clock
bound, including memory failures and exceptions from field validation. -/
theorem evaluate_blobHashes_loop_independent_outer_prefix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeBuffer : watchedArray.toNat + watchedCount.toNat * 16 ≤ buffer.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state blobHashesLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : BlobHashesLoopWitness post array count buffer input inputLength scratch frame ceiling,
        next.index = count ∧ RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (BlobHashesLoopWitness current array count buffer input inputLength scratch frame ceiling) ∧
      RlpSliceInputPrefix current watchedArray watchedInput watchedLength watchedCount.toNat
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : BlobHashesLoopWitness current array count buffer input inputLength scratch frame ceiling,
      blobHashesRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [blobHashesRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) =
      some (.val (.word (if blobHashesRank count current = 0 then 0 else 1))) := by
    rintro current ⟨⟨witness⟩,watched⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : blobHashesRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : blobHashesRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨⟨witness⟩,watched⟩
    refine ⟨⟨witness.decClock⟩,?_⟩
    intro slot inside
    obtain ⟨p,n,item⟩ := watched slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame current _ watchedArray slot p n watchedInput watchedLength item rfl rfl rfl⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      blobHashesRank count (decClockHOLFinite current) = blobHashesRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < blobHashesRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current blobHashesStep = (none,post) ∧ invariant post ∧
          blobHashesRank count post < blobHashesRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current blobHashesStep = (some result,post))) := by
    rintro current ⟨⟨witness⟩,watched⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    have bounded := evaluate_blobHashes_step_bounded current array count witness.index buffer input inputLength scratch frame ceiling inputLimit
      witness.listLocal witness.bufferLocal witness.indexLocal witness.slices inside inputBound limitBound witness.scratchGlobal witness.frameGlobal
      witness.code orderedFrame framePositive scratchBelow witness.arena ticks
    have control := evaluate_blobHashes_step_control current
    cases run : evaluateHOLFiniteState current blobHashesStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := blobHashes_loop_witness_step current post array count buffer input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits ticks run
        have retained := blobHashes_step_normal_independent_outer_prefix current post array count witness.index buffer input inputLength scratch frame ceiling inputLimit
          witness.listLocal witness.bufferLocal witness.indexLocal witness.slices inside inputBound limitBound witness.scratchGlobal witness.frameGlobal
          witness.code orderedFrame framePositive scratchBelow witness.arena ticks watchedArray watchedCount watchedInput watchedLength watched watchedBeforeFrame watchedBeforeBuffer aligned
          (by have factor := Nat.mul_le_mul_right 32 inside; omega) run
        exact Or.inl ⟨rfl,⟨⟨next⟩,retained⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) blobHashesStep
    invariant (blobHashesRank count) cost guard enter entryRank step state ⟨⟨valid⟩,watchedValid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_blobHashes_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨⟨next⟩,retained⟩,zero⟩ := done normal
    refine ⟨next,BitVec.eq_of_toNat_eq ?_,retained⟩
    rw [rankEq post next] at zero
    have bounded := next.indexBound
    omega

#print axioms evaluate_blobHashes_loop_independent_outer_prefix_bounded
end InitECandidate.Runtime

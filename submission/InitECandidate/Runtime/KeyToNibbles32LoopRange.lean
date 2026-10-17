import InitECandidate.Runtime.KeyToNibblesMainRange
import InitECandidate.Runtime.KeyToNibbles32MainBound
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original full-block loop for a 32-byte trie key needs at most eight
source ticks. Invalid byte accesses exit early, without timeout. -/
theorem evaluate_keyToNibbles32_main_loop_range {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 64 → state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (ticks : 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesMainLoop = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → TrieNibbleRange post out 64) ∧
      (∀ output, result ≠ some (.returned output)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => KeyToNibbles32Invariant current ∧
    current.locals.lookup (ofString "key") = some (.val (.word key)) ∧
    current.locals.lookup (ofString "out") = some (.val (.word out)) ∧
    current.memaddrs = state.memaddrs ∧
    ∀ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) →
      TrieNibbleRange current out (2 * index)
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) =
        some (.val (.word (if keyToNibbles32Rank current = 0 then 0 else 1))) := by
    rintro current ⟨⟨⟨index,localIndex,bounded,aligned⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩
    have rankEq : keyToNibbles32Rank current = 8 - index.toNat / 4 := by simp [keyToNibbles32Rank,localIndex]
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    by_cases done : index.toNat = 32
    · have zero : keyToNibbles32Rank current = 0 := by rw [rankEq,done]
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,zero]
      apply BitVec.lt_def.mpr
      change 32 < (index + 4).toNat
      rw [nextNat]
      omega
    · have positive : keyToNibbles32Rank current ≠ 0 := by rw [rankEq]; omega
      have inside : (index + 4) ≤ (32 : BitVec 64) := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        change index.toNat + 4 ≤ 32
        omega
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,positive]
      exact inside
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyToNibbles32Rank (decClockHOLFinite current) = keyToNibbles32Rank current := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyToNibbles32Rank current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesMainStep = (none,post) ∧ invariant post ∧ keyToNibbles32Rank post < keyToNibbles32Rank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesMainStep = (some result,post))) := by
    rintro current ⟨⟨⟨index,localIndex,bounded,aligned⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩ positive _
    have rankEq : keyToNibbles32Rank current = 8 - index.toNat / 4 := by simp [keyToNibbles32Rank,localIndex]
    have inside : index.toNat < 32 := by rw [rankEq] at positive; omega
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    have inputAccess : ∀ offset : Nat, offset < 4 →
        current.memaddrs (panByteAlignHOL (key + (index + BitVec.ofNat 64 offset))) := by
      intro offset small
      rw [domainNow]
      have address : index + BitVec.ofNat 64 offset = BitVec.ofNat 64 (index.toNat + offset) := by simp [BitVec.ofNat_add]
      rw [address]
      exact sourceDomain _ (by omega)
    have outputAccess : ∀ offset : Nat, offset < 8 →
        current.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))) := by
      intro offset small
      rw [domainNow]
      have address : 2 * index + BitVec.ofNat 64 offset = BitVec.ofNat 64 (2 * index.toNat + offset) := by
        simp [BitVec.ofNat_add,BitVec.ofNat_mul]
      rw [address]
      exact outputDomain _ (by omega)
    have indexBound : index.toNat ≤ 28 := by omega
    obtain ⟨post,run,range,nextLocal,clock⟩ := evaluate_keyToNibbles_main_range current key out index
      keyNow outNow localIndex indexBound (rangeNow index localIndex) inputAccess outputAccess
    obtain ⟨result,framed,frameRun,_,locals,_⟩ := evaluate_keyToNibbles_main_step_frame current index localIndex
    have same := frameRun.symm.trans run
    have postEq : framed = post := (Prod.mk.inj same).2
    subst framed
    have metadata := evaluateHOLFiniteState_metadata current keyToNibblesMainStep
    rw [run] at metadata
    dsimp only at metadata
    have oldInvariant : KeyToNibbles32Invariant post :=
      ⟨⟨index + 4,nextLocal,by rw [nextNat]; omega,by rw [nextNat]; omega⟩,
        (locals (ofString "n") (by decide)).trans localN⟩
    have postValid : invariant post := by
      refine ⟨oldInvariant,(locals _ (by decide)).trans keyNow,
        (locals _ (by decide)).trans outNow,metadata.2.1.trans domainNow,?_⟩
      intro other binding
      have equal : other = index + 4 := by simpa using (Option.some.inj (binding.symm.trans nextLocal))
      subst other
      exact range
    have rankPost : keyToNibbles32Rank post = 8 - (index + 4).toNat / 4 := by simp [keyToNibbles32Rank,nextLocal]
    exact ⟨post,by omega,by omega,Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩⟩
  have initialRank : keyToNibbles32Rank state = 8 := by simp [keyToNibbles32Rank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) keyToNibblesMainStep invariant keyToNibbles32Rank 0 guard enter sameRank step
    state (by
      refine ⟨⟨⟨0,initial,by decide,by decide⟩,nLocal⟩,keyLocal,outLocal,rfl,?_⟩
      intro index binding
      have zero : index = 0 := by simpa using (Option.some.inj (binding.symm.trans initial))
      subst index
      intro offset inside
      simp at inside) (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_main_loop]
  refine ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨valid,zeroRank⟩ := completed normal
  obtain ⟨⟨index,binding,bounded,aligned⟩,localN⟩ := valid.1
  have atEnd : index.toNat = 32 := by
    simp [keyToNibbles32Rank,binding] at zeroRank
    omega
  have indexEq : index = 32 := BitVec.eq_of_toNat_eq atEnd
  have range := valid.2.2.2.2 index binding
  subst index
  exact range

#print axioms evaluate_keyToNibbles32_main_loop_range
end InitECandidate.Runtime

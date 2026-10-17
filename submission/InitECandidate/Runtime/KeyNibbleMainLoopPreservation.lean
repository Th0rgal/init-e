import InitECandidate.Runtime.KeyToNibblesGeneralMainLoop
import InitECandidate.Runtime.KeyNibbleMainPreservation
import InitECandidate.Runtime.KeyToNibblesGeneralMainRange
import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original main loop establishes a valid nibble prefix for any bounded
input length, leaving at most three input bytes for its tail loop. -/
theorem evaluate_keyToNibbles_general_main_loop_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out length : BitVec 64)
    (watched watchedLength : BitVec 64)
    (watchedValid : TrieNibbleRange state watched watchedLength)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceDomain : ∀ offset : Nat, offset < length.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat → state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat / 4 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesMainLoop = (result,post) ∧
      state.clock ≤ post.clock + length.toNat / 4 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ index : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat ∧
        length.toNat - index.toNat < 4 ∧ TrieNibbleRange post out (2 * index) ∧
        post.locals.lookup (ofString "key") = some (.val (.word key)) ∧
        post.locals.lookup (ofString "out") = some (.val (.word out)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length)) ∧ post.memaddrs = state.memaddrs ∧ TrieNibbleRange post watched watchedLength) ∧
      (∀ output, result ≠ some (.returned output)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => (((∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
    current.locals.lookup (ofString "n") = some (.val (.word length))) ∧
    current.locals.lookup (ofString "key") = some (.val (.word key)) ∧
    current.locals.lookup (ofString "out") = some (.val (.word out)) ∧
    current.memaddrs = state.memaddrs ∧
    ∀ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) →
      TrieNibbleRange current out (2 * index)) ∧ TrieNibbleRange current watched watchedLength
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) =
        some (.val (.word (if keyNibbleMainRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨⟨⟨index,localIndex,bounded⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩,watchedNow⟩
    have rankEq : keyNibbleMainRank length current = (length.toNat - index.toNat) / 4 := by simp [keyNibbleMainRank,localIndex]
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    by_cases done : keyNibbleMainRank length current = 0
    · simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,done]
      apply BitVec.lt_def.mpr
      change length.toNat < (index + (4 : BitVec 64)).toNat
      rw [nextNat]
      rw [rankEq] at done
      omega
    · have inside : index + 4 ≤ length := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,done]
      exact inside
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyNibbleMainRank length (decClockHOLFinite current) = keyNibbleMainRank length current := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyNibbleMainRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesMainStep = (none,post) ∧ invariant post ∧ keyNibbleMainRank length post < keyNibbleMainRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesMainStep = (some result,post))) := by
    rintro current ⟨⟨⟨⟨index,localIndex,bounded⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩,watchedNow⟩ positive _
    have rankEq : keyNibbleMainRank length current = (length.toNat - index.toNat) / 4 := by simp [keyNibbleMainRank,localIndex]
    have inside : index.toNat + 4 ≤ length.toNat := by rw [rankEq] at positive; omega
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
    have indexBound : 2 * index.toNat + 8 < 2^64 := by omega
    obtain ⟨post,run,range,nextLocal,clock⟩ := evaluate_keyToNibbles_main_range_no_wrap current key out index
      keyNow outNow localIndex indexBound (rangeNow index localIndex) inputAccess outputAccess
    obtain ⟨preserved,preserveRun,preserve,_,_⟩ := evaluate_keyToNibbles_main_preserves current key out index
      keyNow outNow localIndex inputAccess outputAccess
    have preservedEq : preserved = post := (Prod.mk.inj (preserveRun.symm.trans run)).2
    subst preserved
    obtain ⟨result,framed,frameRun,_,locals,_⟩ := evaluate_keyToNibbles_main_step_frame current index localIndex
    have same := frameRun.symm.trans run
    have postEq : framed = post := (Prod.mk.inj same).2
    subst framed
    have metadata := evaluateHOLFiniteState_metadata current keyToNibblesMainStep
    rw [run] at metadata
    dsimp only at metadata
    have oldInvariant : (∃ index : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length)) :=
      ⟨⟨index + 4,nextLocal,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
    have postValid : invariant post := by
      refine ⟨⟨oldInvariant,(locals _ (by decide)).trans keyNow,
        (locals _ (by decide)).trans outNow,metadata.2.1.trans domainNow,?_⟩,preserve watched watchedLength watchedNow⟩
      intro other binding
      have equal : other = index + 4 := by simpa using (Option.some.inj (binding.symm.trans nextLocal))
      subst other
      exact range
    have rankPost : keyNibbleMainRank length post = (length.toNat - (index + 4).toNat) / 4 := by simp [keyNibbleMainRank,nextLocal]
    exact ⟨post,by omega,by omega,Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩⟩
  have initialRank : keyNibbleMainRank length state = length.toNat / 4 := by simp [keyNibbleMainRank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) keyToNibblesMainStep invariant (keyNibbleMainRank length) 0 guard enter sameRank step
    state (by
      refine ⟨⟨⟨⟨0,initial,Nat.zero_le _⟩,nLocal⟩,keyLocal,outLocal,rfl,?_⟩,watchedValid⟩
      intro index binding
      have zero : index = 0 := by simpa using (Option.some.inj (binding.symm.trans initial))
      subst index
      intro offset inside
      simp at inside) (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_main_loop]
  refine ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨valid,zeroRank⟩ := completed normal
  have watchedPost := valid.2
  have valid := valid.1
  obtain ⟨⟨index,binding,bounded⟩,localN⟩ := valid.1
  have remainder : length.toNat - index.toNat < 4 := by
    simp [keyNibbleMainRank,binding] at zeroRank
    omega
  exact ⟨index,binding,bounded,remainder,valid.2.2.2.2 index binding,
    valid.2.1,valid.2.2.1,localN,valid.2.2.2.1,watchedPost⟩

#print axioms evaluate_keyToNibbles_general_main_loop_preserves
end InitECandidate.Runtime

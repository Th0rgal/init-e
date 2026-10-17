import InitECandidate.Runtime.KeyToNibblesGeneralTailLoop
import InitECandidate.Runtime.KeyNibbleTailPreservation
import InitECandidate.Runtime.KeyToNibblesGeneralTailRange
import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original tail loop completes the nibble range in at most the number
of remaining input bytes. -/
theorem evaluate_keyToNibbles_general_tail_loop_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out length start : BitVec 64)
    (watched watchedLength : BitVec 64)
    (watchedValid : TrieNibbleRange state watched watchedLength)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceDomain : ∀ offset : Nat, offset < length.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat → state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (initial : state.locals.lookup (ofString "i") = some (.val (.word start)))
    (startBound : start.toNat ≤ length.toNat)
    (initialRange : TrieNibbleRange state out (2 * start))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : (length.toNat - start.toNat) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesTailLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - start.toNat) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ index : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat ∧
        index = length ∧ TrieNibbleRange post out (2 * index) ∧
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
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if keyNibbleTailRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨⟨⟨index,localIndex,bounded⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩,watchedNow⟩
    have rankEq : keyNibbleTailRank length current = (length.toNat - index.toNat) := by simp [keyNibbleTailRank,localIndex]
    by_cases done : keyNibbleTailRank length current = 0
    · have equal : index = length := by
        apply BitVec.eq_of_toNat_eq
        rw [rankEq] at done
        omega
      simp [evalHOLFinite,evalHOLExact,localIndex,localN,Compiler.Encoders.Asm.wordCmpHOL,done,equal]
    · have inside : index < length := by
        apply BitVec.lt_def.mpr
        rw [rankEq] at done
        omega
      simp [evalHOLFinite,evalHOLExact,localIndex,localN,Compiler.Encoders.Asm.wordCmpHOL,done,inside]
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyNibbleTailRank length (decClockHOLFinite current) = keyNibbleTailRank length current := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyNibbleTailRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesTailStep = (none,post) ∧ invariant post ∧ keyNibbleTailRank length post < keyNibbleTailRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesTailStep = (some result,post))) := by
    rintro current ⟨⟨⟨⟨index,localIndex,bounded⟩,localN⟩,keyNow,outNow,domainNow,rangeNow⟩,watchedNow⟩ positive _
    have rankEq : keyNibbleTailRank length current = (length.toNat - index.toNat) := by simp [keyNibbleTailRank,localIndex]
    have inside : index.toNat < length.toNat := by rw [rankEq] at positive; omega
    have nextNat : (index + 1).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2^64; omega)]
      rfl
    have inputAccess : current.memaddrs (panByteAlignHOL (key + index)) := by
      rw [domainNow]
      simpa using sourceDomain index.toNat inside
    have outputAccess : ∀ offset : Nat, offset < 2 →
        current.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))) := by
      intro offset small
      rw [domainNow]
      have address : 2 * index + BitVec.ofNat 64 offset = BitVec.ofNat 64 (2 * index.toNat + offset) := by
        simp [BitVec.ofNat_add,BitVec.ofNat_mul]
      rw [address]
      exact outputDomain _ (by omega)
    obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64, current.memory (panByteAlignHOL (key + index)) = .word cell := by
      cases current.memory (panByteAlignHOL (key + index)) with
      | word cell => exact ⟨cell,rfl⟩
    let byte := panGetByteHOL (key + index) cell current.be
    have loaded : @panMemLoadByteHOL 64 _ current.memory current.memaddrs
        (fun address => Classical.propDecidable (current.memaddrs address)) current.be (key + index) = some byte := by
      simp [panMemLoadByteHOL,inputAccess,cellRead,byte]
    have indexBound : (2 * index).toNat + 2 < 2^64 := by
      have doubled : (2 * index).toNat = 2 * index.toNat := by
        rw [BitVec.toNat_mul]; change (2 * index.toNat) % 2^64 = _
        exact Nat.mod_eq_of_lt (by omega)
      rw [doubled]; omega
    obtain ⟨post,run,range,nextLocal,clock⟩ := evaluate_keyToNibbles_tail_range_no_wrap current key out index byte
      keyNow outNow localIndex loaded indexBound (rangeNow index localIndex)
      (by simpa using outputAccess 0 (by omega)) (by simpa using outputAccess 1 (by omega))
    obtain ⟨preserved,preserveRun,preserve,_,_⟩ := evaluate_keyToNibbles_tail_preserves current key out index
      keyNow outNow localIndex inputAccess (by simpa using outputAccess 0 (by omega)) (by simpa using outputAccess 1 (by omega))
    have preservedEq : preserved = post := (Prod.mk.inj (preserveRun.symm.trans run)).2
    subst preserved
    obtain ⟨result,framed,frameRun,_,locals,_⟩ := evaluate_keyToNibbles_tail_step_frame current index localIndex
    have same := frameRun.symm.trans run
    have postEq : framed = post := (Prod.mk.inj same).2
    subst framed
    have metadata := evaluateHOLFiniteState_metadata current keyToNibblesTailStep
    rw [run] at metadata
    dsimp only at metadata
    have oldInvariant : (∃ index : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length)) :=
      ⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
    have postValid : invariant post := by
      refine ⟨⟨oldInvariant,(locals _ (by decide)).trans keyNow,
        (locals _ (by decide)).trans outNow,metadata.2.1.trans domainNow,?_⟩,preserve watched watchedLength watchedNow⟩
      intro other binding
      have equal : other = index + 1 := by simpa using (Option.some.inj (binding.symm.trans nextLocal))
      subst other
      exact range
    have rankPost : keyNibbleTailRank length post = (length.toNat - (index + 1).toNat) := by simp [keyNibbleTailRank,nextLocal]
    exact ⟨post,by omega,by omega,Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩⟩
  have initialRank : keyNibbleTailRank length state = (length.toNat - start.toNat) := by simp [keyNibbleTailRank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) keyToNibblesTailStep invariant (keyNibbleTailRank length) 0 guard enter sameRank step
    state (by
      refine ⟨⟨⟨⟨start,initial,startBound⟩,nLocal⟩,keyLocal,outLocal,rfl,?_⟩,watchedValid⟩
      intro index binding
      have equal : index = start := by simpa using (Option.some.inj (binding.symm.trans initial))
      subst index
      exact initialRange) (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_tail_loop]
  refine ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨valid,zeroRank⟩ := completed normal
  have watchedPost := valid.2
  have valid := valid.1
  obtain ⟨⟨index,binding,bounded⟩,localN⟩ := valid.1
  have remainder : index = length := by
    apply BitVec.eq_of_toNat_eq
    simp [keyNibbleTailRank,binding] at zeroRank
    omega
  exact ⟨index,binding,bounded,remainder,valid.2.2.2.2 index binding,
    valid.2.1,valid.2.2.1,localN,valid.2.2.2.1,watchedPost⟩

#print axioms evaluate_keyToNibbles_general_tail_loop_preserves
end InitECandidate.Runtime

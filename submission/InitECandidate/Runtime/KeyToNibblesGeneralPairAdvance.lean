import InitECandidate.Runtime.KeyToNibblesGeneralPair
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_keyNibble_pair_advance_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : (2 * index).toNat + 2 < 2^64)
    (valid : TrieNibbleRange state out (2 * index))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + 2 * index)))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + 1)))) :
    ∃ post, evaluateHOLFiniteState state (.seq (keyNibblePair name) (memzeroAdvance 1)) = (none,post) ∧
      TrieNibbleRange post out (2 * (index + 1)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.clock = state.clock := by
  obtain ⟨middle,run,range,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_offset_pair_no_wrap state name 0 byte out index outLocal indexLocal byteLocal
      (by simpa using bounded) (by simpa using valid) (by simpa using firstDomain) (by simpa using secondDomain)
  have runPair : evaluateHOLFiniteState state (keyNibblePair name) = (none,middle) := by
    simpa [keyNibblePair,keyNibbleOffsetPair] using run
  have indexNow : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals]; exact indexLocal
  have advance := evaluate_memzero_advance middle index 1 indexNow
  have arithmetic : 2 * index + 1 + 1 = 2 * (index + 1) := by
    simp [BitVec.mul_add,BitVec.add_assoc]
  refine ⟨setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle,?_,?_,?_,clock⟩
  · rw [evaluateHOLFiniteState_seq_line780,runPair]
    exact advance
  · rw [← arithmetic]
    have preserved := range.after_frame (post := setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle) rfl rfl rfl
    simpa using preserved
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_keyNibble_pair_advance_no_wrap
end InitECandidate.Runtime

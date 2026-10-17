import InitECandidate.Runtime.KeyNibbleByteScopePreservation
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A full original tail iteration preserves every existing nibble range,
including the optional nibble already written by the compact decoder. -/
theorem evaluate_keyToNibbles_tail_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out index : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceDomain : state.memaddrs (panByteAlignHOL (key + index)))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + 2 * index)))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + 1)))) :
    ∃ post, evaluateHOLFiniteState state keyToNibblesTailStep = (none,post) ∧
      (∀ nibs length, TrieNibbleRange state nibs length → TrieNibbleRange post nibs length) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.clock = state.clock := by
  obtain ⟨byte,middle,run,preserve,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_byte_scope_preserves state (ofString "b") 0 (memzeroAdvance 1) key out index
      (by decide) (by decide) keyLocal outLocal indexLocal
      (by simpa using sourceDomain) (by simpa using firstDomain) (by simpa using secondDomain)
  have atIndex : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "i" by decide] using indexLocal
  have advance := evaluate_memzero_advance middle index 1 atIndex
  let output := setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "b",state.locals.lookup (ofString "b"))}
  have source : keyToNibblesTailStep = keyNibbleByteThen (ofString "b") 0 (memzeroAdvance 1) := by
    rw [source_keyNibble_tail_step]
    rfl
  refine ⟨post,?_,?_,?_,clock⟩
  · rw [source,run]
    change (let result := evaluateHOLFiniteState middle (memzeroAdvance 1); _) = _
    rw [advance]
  · intro nibs length valid
    exact (preserve nibs length valid).after_frame rfl rfl rfl
  · change (HolFiniteMapExact.resVarEq _ _).lookup _ = _
    rw [saved_local_lookup_other _ _ _ _ (by decide)]
    simp [output,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_keyToNibbles_tail_preserves
end InitECandidate.Runtime

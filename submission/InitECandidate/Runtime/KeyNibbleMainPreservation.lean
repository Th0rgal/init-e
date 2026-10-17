import InitECandidate.Runtime.KeyNibbleByteScopePreservation
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_keyToNibbles_main_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out index : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceDomain : ∀ offset : Nat, offset < 4 →
      state.memaddrs (panByteAlignHOL (key + (index + BitVec.ofNat 64 offset))))
    (outputDomain : ∀ offset : Nat, offset < 8 →
      state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset)))) :
    ∃ post, evaluateHOLFiniteState state keyToNibblesMainStep = (none,post) ∧
      (∀ nibs length, TrieNibbleRange state nibs length → TrieNibbleRange post nibs length) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 4))) ∧
      post.clock = state.clock := by
  let c4 : ProgHOL 64 := memzeroAdvance 4
  let c3 : ProgHOL 64 := keyNibbleByteThen (ofString "b3") 3 c4
  let c2 : ProgHOL 64 := keyNibbleByteThen (ofString "b2") 2 c3
  let c1 : ProgHOL 64 := keyNibbleByteThen (ofString "b1") 1 c2
  let c0 : ProgHOL 64 := keyNibbleByteThen (ofString "b0") 0 c1
  have source : keyToNibblesMainStep = c0 := source_keyNibble_main_step
  let s0 := state
  have key0 := keyLocal
  have out0 := outLocal
  have index0 := indexLocal
  have domain0 : s0.memaddrs = state.memaddrs := rfl
  have clock0 : s0.clock = state.clock := rfl
  obtain ⟨byte0,s1,q0,r1,locals1,tick1,dom1,endian1⟩ :=
    evaluate_keyNibble_byte_scope_preserves s0 (ofString "b0") 0 c1 key out index
      (by decide) (by decide) key0 out0 index0
      (by rw [domain0]; exact sourceDomain 0 (by decide))
      (by rw [domain0]; exact outputDomain 0 (by decide))
      (by rw [domain0]; simpa [BitVec.add_assoc] using outputDomain 1 (by decide))
  have domain1 : s1.memaddrs = state.memaddrs := dom1.trans domain0
  have clock1 : s1.clock = state.clock := tick1.trans clock0
  have key1 : s1.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [locals1]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b0" ≠ ofString "key" by decide] using key0
  have out1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [locals1]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b0" ≠ ofString "out" by decide] using out0
  have index1 : s1.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals1]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b0" ≠ ofString "i" by decide] using index0
  obtain ⟨byte1,s2,q1,r2,locals2,tick2,dom2,endian2⟩ :=
    evaluate_keyNibble_byte_scope_preserves s1 (ofString "b1") 1 c2 key out index
      (by decide) (by decide) key1 out1 index1
      (by rw [domain1]; exact sourceDomain 1 (by decide))
      (by rw [domain1]; exact outputDomain 2 (by decide))
      (by rw [domain1]; simpa [BitVec.add_assoc] using outputDomain 3 (by decide))
  have domain2 : s2.memaddrs = state.memaddrs := dom2.trans domain1
  have clock2 : s2.clock = state.clock := tick2.trans clock1
  have key2 : s2.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [locals2]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b1" ≠ ofString "key" by decide] using key1
  have out2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [locals2]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b1" ≠ ofString "out" by decide] using out1
  have index2 : s2.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals2]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b1" ≠ ofString "i" by decide] using index1
  obtain ⟨byte2,s3,q2,r3,locals3,tick3,dom3,endian3⟩ :=
    evaluate_keyNibble_byte_scope_preserves s2 (ofString "b2") 2 c3 key out index
      (by decide) (by decide) key2 out2 index2
      (by rw [domain2]; exact sourceDomain 2 (by decide))
      (by rw [domain2]; exact outputDomain 4 (by decide))
      (by rw [domain2]; simpa [BitVec.add_assoc] using outputDomain 5 (by decide))
  have domain3 : s3.memaddrs = state.memaddrs := dom3.trans domain2
  have clock3 : s3.clock = state.clock := tick3.trans clock2
  have key3 : s3.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [locals3]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b2" ≠ ofString "key" by decide] using key2
  have out3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [locals3]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b2" ≠ ofString "out" by decide] using out2
  have index3 : s3.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals3]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b2" ≠ ofString "i" by decide] using index2
  obtain ⟨byte3,s4,q3,r4,locals4,tick4,dom4,endian4⟩ :=
    evaluate_keyNibble_byte_scope_preserves s3 (ofString "b3") 3 c4 key out index
      (by decide) (by decide) key3 out3 index3
      (by rw [domain3]; exact sourceDomain 3 (by decide))
      (by rw [domain3]; exact outputDomain 6 (by decide))
      (by rw [domain3]; simpa [BitVec.add_assoc] using outputDomain 7 (by decide))
  have domain4 : s4.memaddrs = state.memaddrs := dom4.trans domain3
  have clock4 : s4.clock = state.clock := tick4.trans clock3
  have key4 : s4.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [locals4]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b3" ≠ ofString "key" by decide] using key3
  have out4 : s4.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [locals4]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b3" ≠ ofString "out" by decide] using out3
  have index4 : s4.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals4]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b3" ≠ ofString "i" by decide] using index3
  have advance := evaluate_memzero_advance s4 index 4 index4
  let output := setVarHOLFinite (ofString "i") (.val (.word (index + 4))) s4
  let p3 := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "b3",s3.locals.lookup (ofString "b3"))}
  have run3 : evaluateHOLFiniteState s3 c3 = (none,p3) := by
    rw [q3]
    change (let result := evaluateHOLFiniteState s4 (memzeroAdvance 4); _) = _
    rw [advance]
  let p2 := {p3 with locals := HolFiniteMapExact.resVarEq p3.locals (ofString "b2",s2.locals.lookup (ofString "b2"))}
  have run2 : evaluateHOLFiniteState s2 c2 = (none,p2) := by
    rw [q2]
    rw [run3]
  let p1 := {p2 with locals := HolFiniteMapExact.resVarEq p2.locals (ofString "b1",s1.locals.lookup (ofString "b1"))}
  have run1 : evaluateHOLFiniteState s1 c1 = (none,p1) := by
    rw [q1]
    rw [run2]
  let p0 := {p1 with locals := HolFiniteMapExact.resVarEq p1.locals (ofString "b0",s0.locals.lookup (ofString "b0"))}
  have run0 : evaluateHOLFiniteState s0 c0 = (none,p0) := by
    rw [q0]
    rw [run1]
  refine ⟨p0,?_,?_,?_,clock4⟩
  · rw [source]; exact run0
  · intro nibs length valid
    exact (r4 nibs length (r3 nibs length (r2 nibs length (r1 nibs length valid)))).after_frame rfl rfl rfl
  · change (HolFiniteMapExact.resVarEq _ _).lookup _ = _
    simp only [p1,p2,p3]
    repeat rw [saved_local_lookup_other _ _ _ _ (by decide)]
    simp [output,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_keyToNibbles_main_preserves
end InitECandidate.Runtime

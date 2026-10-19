import InitECandidate.Runtime.StatelessWitnessCheckedEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The three actual offset loads bind the accepted offsets without changing
memory/globals/domain. A returned suffix exposes the real three-list execution
and the ordering checked in the source. -/
theorem stateless_witness_loaded_entry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (offsets length : BitVec 64) (v : ValueHOL 64)
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (checked : SszCheckOffsetsReturned s offsets 3 12 length (.val (.word 0)))
    (run : evaluateHOLFiniteState s (statelessAt 36) = (some (.returned v),post)) :
    ∃ (ready output : PanSemStateFiniteExact 64 F) (middle last : BitVec 64),
      evaluateHOLFiniteState ready (statelessAt 39) = (some (.returned v),output) ∧
      ready.locals.lookup (ofString "w0") = some (.val (.word (12#64))) ∧
      ready.locals.lookup (ofString "w1") = some (.val (.word middle)) ∧
      ready.locals.lookup (ofString "w2") = some (.val (.word last)) ∧
      (∀ key : MlS, key ≠ ofString "w0" → key ≠ ofString "w1" → key ≠ ofString "w2" →
        ready.locals.lookup key = s.locals.lookup key) ∧
      ready.memory = s.memory ∧ ready.globals = s.globals ∧ ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧
      12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ length.toNat := by
  obtain ⟨_,accepted,first⟩ := checked
  have firstFacts := first (by decide)
  let middle := memWord s.memory (offsets + (8#64))
  let last := memWord s.memory (offsets + (16#64))
  have d8 : s.memaddrs (offsets + (8#64)) := by simpa using (accepted (1#64) (by decide)).1
  have d16 : s.memaddrs (offsets + (16#64)) := by simpa using (accepted (2#64) (by decide)).1
  have bounds := stateless_witness_offset_bounds s offsets length (12#64) middle last firstFacts.2 accepted firstFacts.2 rfl rfl
  have load0 := eval_load_mem_word s (.var .global (ofString "ssz_offs")) offsets
    (by simp [evalHOLExact,atOffsets]) firstFacts.1
  rw [firstFacts.2] at load0
  rw [source_stateless_witness_load0] at run
  obtain ⟨v0,o0,init0,run1,e0⟩ := evaluate_dec_returned_scope s post (ofString "w0") .one _ _ v run
  have eq0 : v0 = .val (.word (12#64)) := Option.some.inj (init0.symm.trans load0)
  subst eq0
  let one := setVarHOLFinite (ofString "w0") (.val (.word (12#64))) s
  have load1 := eval_load_mem_word one (.op .add [.var .global (ofString "ssz_offs"),.const 8]) (offsets + (8#64))
    (by simp [one,setVarHOLFinite,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord]) d8
  rw [source_stateless_witness_load1] at run1
  obtain ⟨v1,o1,init1,run2,e1⟩ := evaluate_dec_returned_scope one o0 (ofString "w1") .one _ _ v run1
  have eq1 : v1 = .val (.word middle) := Option.some.inj (init1.symm.trans load1)
  subst eq1
  let two := setVarHOLFinite (ofString "w1") (.val (.word middle)) one
  have load2 := eval_load_mem_word two (.op .add [.var .global (ofString "ssz_offs"),.const 16]) (offsets + (16#64))
    (by simp [two,one,setVarHOLFinite,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord]) d16
  rw [source_stateless_witness_load2] at run2
  obtain ⟨v2,o2,init2,run3,e2⟩ := evaluate_dec_returned_scope two o1 (ofString "w2") .one _ _ v run2
  have eq2 : v2 = .val (.word last) := Option.some.inj (init2.symm.trans load2)
  subst eq2
  let ready := setVarHOLFinite (ofString "w2") (.val (.word last)) two
  refine ⟨ready,o2,middle,last,run3,?_,?_,?_,?_,rfl,rfl,rfl,rfl,?_,?_,bounds.2.1,bounds.2.2.1,bounds.2.2.2⟩
  · simp (config := {decide := true}) [ready,two,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [ready,two,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key h0 h1 h2
    simp [ready,two,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm h0,Ne.symm h1,Ne.symm h2]
  · rw [e0]; show o0.memory = _; rw [e1]; show o1.memory = _; rw [e2]
  · rw [e0]; show o0.globals = _; rw [e1]; show o1.globals = _; rw [e2]

#print axioms stateless_witness_loaded_entry
end InitECandidate.Runtime

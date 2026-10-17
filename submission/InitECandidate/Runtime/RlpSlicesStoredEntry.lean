import InitECandidate.Runtime.TxFixedBytesArguments
import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual two slice stores and counter assignments establish the concrete
entry consumed by fixed-byte extraction. -/
theorem evaluate_rlpSlices_updates_entry_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64)) :
    ∃ post, evaluateHOLFiniteState state rlpSlicesUpdates = (none,post) ∧
      RlpSliceEntry post array index (pointer + offset) total ∧ post.clock = state.clock ∧ post.memaddrs = state.memaddrs ∧
      (∀ cell, cell ≠ array + index * 16#64 → cell ≠ array + index * 16#64 + 8#64 →
        post.memory cell = state.memory cell) := by
  let address := array + index * 16#64
  have separate : address ≠ address + 8#64 := by
    intro equal
    have impossible : (0#64) = 8#64 := (BitVec.add_right_inj address).mp (by simpa only [BitVec.add_zero] using equal)
    exact (by decide : (0#64) ≠ 8#64) impossible
  let first := sourceWriteWord state address (pointer + offset)
  let second := sourceWriteWord first (address + 8#64) total
  have one := evaluate_store_word state address (pointer + offset)
    (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16]])
    (.op .add [.var .local (ofString "p"),.var .local (ofString "off")])
    (by simp [address,evalHOLExact,evalListHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord])
    (by simp [evalHOLExact,evalListHOLExact,pointerLocal,offsetLocal,wordOpHOL,wordOp,valueIsWord,valueWord]) domain0
  have two := evaluate_store_word first (address + 8#64) total
    (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])
    (.var .local (ofString "total"))
    (by simp [first,sourceWriteWord,address,evalHOLExact,evalListHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,BitVec.add_assoc])
    (by simpa [first,sourceWriteWord,evalHOLExact] using totalLocal) domain8
  have advances := evaluate_rlpSlices_advances second offset index total offsetLocal indexLocal totalLocal
  let post := setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
    (setVarHOLFinite (ofString "off") (.val (.word (offset + total))) second)
  refine ⟨post,?_,?_,rfl,rfl,?_⟩
  · rw [source_rlpSlices_updates]
    exact evaluate_seq_none one (evaluate_seq_none two advances)
  · refine ⟨domain0,domain8,?_,?_⟩
    · change (if address = address + 8#64 then .word total else
        if address = address then .word (pointer + offset) else state.memory address) = _
      rw [if_neg separate,if_pos rfl]
    · change (if address + 8#64 = address + 8#64 then .word total else first.memory (address + 8#64)) = _
      rw [if_pos rfl]
  · intro cell different0 different8
    change (if cell = address + 8#64 then .word total else
      if cell = address then .word (pointer + offset) else state.memory cell) = _
    rw [if_neg different8,if_neg different0]

theorem evaluate_rlpSlices_updates_entry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64)) :
    ∃ post, evaluateHOLFiniteState state rlpSlicesUpdates = (none,post) ∧
      RlpSliceEntry post array index (pointer + offset) total ∧ post.clock = state.clock := by
  obtain ⟨post,run,entry,clock,_,_⟩ := evaluate_rlpSlices_updates_entry_frame state array index pointer offset total
    arrayLocal indexLocal pointerLocal offsetLocal totalLocal domain0 domain8
  exact ⟨post,run,entry,clock⟩

#print axioms evaluate_rlpSlices_updates_entry_frame

#print axioms evaluate_rlpSlices_updates_entry
end InitECandidate.Runtime

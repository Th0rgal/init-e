import InitECandidate.Runtime.HashInsertValueTail
import InitECandidate.Runtime.HashInsertOccupancyLinked32
import InitECandidate.Runtime.HashTableArraysValue32
import InitECandidate.Runtime.HashOrderLinkedWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual value-write and bookkeeping suffix preserves live order linkage. -/
theorem evaluate_hashInsert_value_linked32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count index value cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (inside : index.toNat < capacity.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ HashOrderLinked used order orderPos capacity (count + 1) post := by
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos count bits
  have d40 : state.memaddrs (table + 40#64) := facts.valuesDomain
  have c40 : state.memory (table + 40#64) = .word values := invariant.cell40
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetValueAddress =
      some (.val (.word (values + index * 8))) := by
    simp [hashSetValueAddress,evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40]
  have store := evaluate_store_word state (values + index * 8) value hashSetValueAddress (.var .local (ofString "value"))
    address valueLocal (facts.valueDomain index inside)
  let written := sourceWriteWord state (values + index * 8) value
  have writtenInvariant := invariant.write_value state table keys stride capacity used values order orderPos count index value bits inside
  have writtenLinked := linked.write_value_layout32 state table keys stride capacity used values order orderPos count index value bits invariant inside
  have separate : panByteAlignHOL (used + index) ≠ values + index * 8#64 := facts.valueSeparate index inside index inside
  have byteAfter : written.memory (panByteAlignHOL (used + index)) = .word cell := by
    simpa [written,sourceWriteWord,separate] using byteMemory
  obtain ⟨post,tail,ticks,postLinked⟩ := evaluate_hashInsert_occupancy_linked32 written
    table keys stride capacity used values order orderPos count index cell bits writtenInvariant writtenLinked inside
    tableLocal orderLocal orderPosLocal usedLocal indexLocal byteAfter
  refine ⟨post,?_,ticks,postLinked⟩
  unfold hashInsertValueTail
  rw [evaluateHOLFiniteState_seq_line780,store]
  exact tail

#print axioms evaluate_hashInsert_value_linked32
end InitECandidate.Runtime

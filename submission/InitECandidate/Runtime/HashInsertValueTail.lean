import InitECandidate.Runtime.HashInsertCountInvariant
import InitECandidate.Runtime.HashSetExisting
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashInsertValueTail : ProgHOL 64 :=
  .seq (.store hashSetValueAddress (.var .local (ofString "value")))
    (.seq hashInsertOccupancyStore hashInsertCountTail)

def sourceFirstCallContinuation (name : MlS) : ProgHOL 64 → Option (ProgHOL 64)
  | .seq (.call _ callee _) rest => if callee == name then some rest else sourceFirstCallContinuation name rest
  | .dec _ _ _ body => sourceFirstCallContinuation name body
  | .decCall _ _ _ _ body => sourceFirstCallContinuation name body
  | .seq first rest => (sourceFirstCallContinuation name first).orElse (fun _ => sourceFirstCallContinuation name rest)
  | _ => none

theorem source_htabInsert_after_copy :
    sourceFirstCallContinuation (ofString "memcpy") (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some hashInsertValueTail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The contiguous post-copy insertion suffix stores the value, marks the
empty slot and increments the header/count invariant without source clocks. -/
theorem evaluate_hashInsert_value_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (valuesDomain : state.memaddrs (table + 40)) (valuesMemory : state.memory (table + 40) = .word values)
    (valueDomain : state.memaddrs (values + index * 8))
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24)) (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (noWrap : count.toNat + 1 < 2 ^ 64)
    (valueCountSeparate : table + 24 ≠ values + index * 8)
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ values + index * 8)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock := by
  have d40 : state.memaddrs (table + 40#64) := valuesDomain
  have c40 : state.memory (table + 40#64) = .word values := valuesMemory
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetValueAddress =
      some (.val (.word (values + index * 8))) := by
    simp [hashSetValueAddress,evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40]
  have store := evaluate_store_word state (values + index * 8) value hashSetValueAddress (.var .local (ofString "value"))
    address valueLocal valueDomain
  let written := sourceWriteWord state (values + index * 8) value
  have literalSeparate : panByteAlignHOL (used + index) ≠ values + index * 8#64 := valueSeparate index inside
  have literalCountSeparate : table + 24#64 ≠ values + index * 8#64 := valueCountSeparate
  have byteAfter : written.memory (panByteAlignHOL (used + index)) = .word cell := by
    simpa [written,sourceWriteWord,literalSeparate] using byteMemory
  have emptyAfter : hashOccupancyRead written used index = some 0 := by
    have same : hashOccupancyRead written used index = hashOccupancyRead state used index := by
      simp [hashOccupancyRead,written,panMemLoadByteHOL,sourceWriteWord,literalSeparate]
      rfl
    exact same.trans empty
  have countAfter : written.memory (table + 24) = .word count := by
    simpa [written,sourceWriteWord,literalCountSeparate] using countMemory
  have agreementAfter : count.toNat = hashOccupiedCount capacity (hashOccupancyRead written used) := by
    rw [sourceWriteWord_occupancy_preserved state capacity used (values + index * 8) value valueSeparate]
    exact agreement
  obtain ⟨post,tail,header,agrees,ticks⟩ := evaluate_hashInsert_count_invariant written capacity used table order orderPos count index cell
    tableLocal orderLocal orderPosLocal usedLocal indexLocal inside byteDomain byteAfter emptyAfter orderDomain orderPosDomain
    countDomain countAfter agreementAfter noWrap separate
  refine ⟨post,?_,header,agrees,ticks⟩
  unfold hashInsertValueTail
  rw [evaluateHOLFiniteState_seq_line780,store]
  exact tail

#print axioms source_htabInsert_after_copy
#print axioms evaluate_hashInsert_value_tail
end InitECandidate.Runtime

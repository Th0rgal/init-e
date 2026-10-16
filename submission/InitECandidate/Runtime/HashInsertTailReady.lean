import InitECandidate.Runtime.HashInsertValueTail
import InitECandidate.Runtime.MemcpyAlignedCombinedCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete facts needed after copying an insertion key. -/
structure HashInsertTailReady {F : Type}
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table))
  orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order))
  orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value))
  inside : index.toNat < capacity.toNat
  valuesDomain : state.memaddrs (table + 40)
  valuesMemory : state.memory (table + 40) = .word values
  valueDomain : state.memaddrs (values + index * 8)
  byteDomain : state.memaddrs (panByteAlignHOL (used + index))
  byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell
  empty : hashOccupancyRead state used index = some 0
  orderDomain : state.memaddrs (order + count * 8)
  orderPosDomain : state.memaddrs (orderPos + index * 8)
  countDomain : state.memaddrs (table + 24)
  countMemory : state.memory (table + 24) = .word count
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)
  noWrap : count.toNat + 1 < 2 ^ 64
  valueCountSeparate : table + 24 ≠ values + index * 8
  valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ values + index * 8
  separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
    panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
    panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24

/-- Copying a key transfers the insertion facts when it preserves the three
header/occupancy words, actual occupancy count, domains and caller locals. -/
theorem HashInsertTailReady.after_copy {F : Type}
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (locals : post.locals = state.locals) (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (valuesWord : post.memory (table + 40) = state.memory (table + 40))
    (countWord : post.memory (table + 24) = state.memory (table + 24))
    (occupancyWord : post.memory (panByteAlignHOL (used + index)) = state.memory (panByteAlignHOL (used + index)))
    (counts : hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used)) :
    HashInsertTailReady capacity used table values value order orderPos count index cell post := by
  have reads : hashOccupancyRead post used index = hashOccupancyRead state used index := by
    have postCell : post.memory (panByteAlignHOL (used + index)) = .word cell := occupancyWord.trans ready.byteMemory
    simp [hashOccupancyRead,panMemLoadByteHOL,postCell,ready.byteMemory,addresses,endian]
    rw [addresses]
  refine {
    tableLocal := by rw [locals]; exact ready.tableLocal
    orderLocal := by rw [locals]; exact ready.orderLocal
    orderPosLocal := by rw [locals]; exact ready.orderPosLocal
    usedLocal := by rw [locals]; exact ready.usedLocal
    indexLocal := by rw [locals]; exact ready.indexLocal
    valueLocal := by rw [locals]; exact ready.valueLocal
    inside := ready.inside
    valuesDomain := by rw [addresses]; exact ready.valuesDomain
    valuesMemory := by rw [valuesWord]; exact ready.valuesMemory
    valueDomain := by rw [addresses]; exact ready.valueDomain
    byteDomain := by rw [addresses]; exact ready.byteDomain
    byteMemory := by rw [occupancyWord]; exact ready.byteMemory
    empty := reads.trans ready.empty
    orderDomain := by rw [addresses]; exact ready.orderDomain
    orderPosDomain := by rw [addresses]; exact ready.orderPosDomain
    countDomain := by rw [addresses]; exact ready.countDomain
    countMemory := by rw [countWord]; exact ready.countMemory
    agreement := by rw [counts]; exact ready.agreement
    noWrap := ready.noWrap
    valueCountSeparate := ready.valueCountSeparate
    valueSeparate := ready.valueSeparate
    separate := ready.separate
  }

/-- Execute the checked original post-copy suffix from its concrete premises. -/
theorem HashInsertTailReady.run {F : Type}
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock := by
  exact evaluate_hashInsert_value_tail state capacity used table values value order orderPos count index cell
    ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.valueLocal ready.inside ready.valuesDomain ready.valuesMemory ready.valueDomain ready.byteDomain ready.byteMemory ready.empty ready.orderDomain ready.orderPosDomain ready.countDomain ready.countMemory ready.agreement ready.noWrap ready.valueCountSeparate ready.valueSeparate ready.separate

#print axioms HashInsertTailReady.run
#print axioms HashInsertTailReady.after_copy
end InitECandidate.Runtime

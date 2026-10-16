import InitECandidate.Runtime.HashInsertHashScope32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Memory/domain/count facts for insertion, independent of header-load locals. -/
structure HashInsertTableMemory {F : Type}
    (capacity used table values order orderPos count : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  valuesDomain : state.memaddrs (table + 40)
  valuesMemory : state.memory (table + 40) = .word values
  valueDomain : ∀ index : BitVec 64, index.toNat < capacity.toNat → state.memaddrs (values + index * 8)
  byteDomain : ∀ index : BitVec 64, index.toNat < capacity.toNat → state.memaddrs (panByteAlignHOL (used + index))
  orderDomain : state.memaddrs (order + count * 8)
  orderPosDomain : ∀ index : BitVec 64, index.toNat < capacity.toNat → state.memaddrs (orderPos + index * 8)
  countDomain : state.memaddrs (table + 24)
  countMemory : state.memory (table + 24) = .word count
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)
  noWrap : count.toNat + 1 < 2 ^ 64
  valueCountSeparate : ∀ index : BitVec 64, index.toNat < capacity.toNat → table + 24 ≠ values + index * 8
  valueSeparate : ∀ index : BitVec 64, index.toNat < capacity.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ values + index * 8
  separate : ∀ index : BitVec 64, index.toNat < capacity.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
    panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
    panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24

/-- Header-load scopes change locals while retaining the table memory facts. -/
theorem HashInsertTableMemory.enter {F : Type}
    (capacity used table values value order orderPos count : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F)
    (facts : HashInsertTableMemory capacity used table values order orderPos count state)
    (memory : post.memory = state.memory) (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (tableLocal : post.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : post.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : post.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : post.locals.lookup (ofString "used") = some (.val (.word used)))
    (valueLocal : post.locals.lookup (ofString "value") = some (.val (.word value)))
    : HashInsertSlotEnvironment capacity used table values value order orderPos count post := by
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext index
    unfold hashOccupancyRead
    rw [memory,addresses,endian]
  refine {
    tableLocal := tableLocal
    orderLocal := orderLocal
    orderPosLocal := orderPosLocal
    usedLocal := usedLocal
    valueLocal := valueLocal
    valuesDomain := by rw [addresses]; exact facts.valuesDomain
    valuesMemory := by rw [memory]; exact facts.valuesMemory
    valueDomain := by rw [addresses]; exact facts.valueDomain
    byteDomain := by rw [addresses]; exact facts.byteDomain
    orderDomain := by rw [addresses]; exact facts.orderDomain
    orderPosDomain := by rw [addresses]; exact facts.orderPosDomain
    countDomain := by rw [addresses]; exact facts.countDomain
    countMemory := by rw [memory]; exact facts.countMemory
    agreement := by rw [reads]; exact facts.agreement
    noWrap := facts.noWrap
    valueCountSeparate := facts.valueCountSeparate
    valueSeparate := facts.valueSeparate
    separate := facts.separate
  }

#print axioms HashInsertTableMemory.enter
end InitECandidate.Runtime

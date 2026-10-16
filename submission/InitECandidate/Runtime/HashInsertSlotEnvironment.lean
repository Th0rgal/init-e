import InitECandidate.Runtime.HashInsertCopyBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shared table facts needed to insert at any empty in-range slot. -/
structure HashInsertSlotEnvironment {F : Type}
    (capacity used table values value order orderPos count : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table))
  orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order))
  orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value))
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

/-- Introducing i at a concrete empty slot derives all post-probe insertion
premises, selecting the actual aligned occupancy word from source memory. -/
theorem HashInsertSlotEnvironment.prepare {F : Type}
    (capacity used table values value order orderPos count : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (environment : HashInsertSlotEnvironment capacity used table values value order orderPos count state)
    (index : BitVec 64) (inside : index.toNat < capacity.toNat)
    (empty : hashOccupancyRead state used index = some 0) :
    ∃ cell : BitVec 64, HashInsertTailReady capacity used table values value order orderPos count index cell
      (setVarHOLFinite (ofString "i") (.val (.word index)) state) := by
  obtain ⟨cell,cellMemory⟩ : ∃ cell : BitVec 64, state.memory (panByteAlignHOL (used + index)) = .word cell := by
    cases state.memory (panByteAlignHOL (used + index)) with | word cell => exact ⟨cell,rfl⟩
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨cell,{
    tableLocal := by change entered.locals.lookup _ = _; rw [other _ (by decide)]; exact environment.tableLocal
    orderLocal := by change entered.locals.lookup _ = _; rw [other _ (by decide)]; exact environment.orderLocal
    orderPosLocal := by change entered.locals.lookup _ = _; rw [other _ (by decide)]; exact environment.orderPosLocal
    usedLocal := by change entered.locals.lookup _ = _; rw [other _ (by decide)]; exact environment.usedLocal
    indexLocal := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    valueLocal := by change entered.locals.lookup _ = _; rw [other _ (by decide)]; exact environment.valueLocal
    inside := inside
    valuesDomain := environment.valuesDomain
    valuesMemory := environment.valuesMemory
    valueDomain := environment.valueDomain index inside
    byteDomain := environment.byteDomain index inside
    byteMemory := cellMemory
    empty := empty
    orderDomain := environment.orderDomain
    orderPosDomain := environment.orderPosDomain index inside
    countDomain := environment.countDomain
    countMemory := environment.countMemory
    agreement := environment.agreement
    noWrap := environment.noWrap
    valueCountSeparate := environment.valueCountSeparate index inside
    valueSeparate := environment.valueSeparate index inside
    separate := environment.separate index inside
  }⟩

#print axioms HashInsertSlotEnvironment.prepare
end InitECandidate.Runtime

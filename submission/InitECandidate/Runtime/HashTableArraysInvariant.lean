import InitECandidate.Runtime.HashTableArraysInvariant32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Relocated table geometry with its actual source key length. -/
structure HashTableArraysInvariant {F : Type}
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  power : capacity.toNat = 2 ^ bits
  keysAligned : keys.toNat % 8 = 0
  strideAligned : stride.toNat % 8 = 0
  valuesAligned : values.toNat % 8 = 0
  usedAligned : used.toNat % 8 = 0
  orderAligned : order.toNat % 8 = 0
  orderPosAligned : orderPos.toNat % 8 = 0
  headerKeys : table.toNat + 72 ≤ keys.toNat
  headerValues : table.toNat + 72 ≤ values.toNat
  keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat
  valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat
  usedBefore : used.toNat + capacity.toNat ≤ order.toNat
  orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat
  endBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496
  fits : keyLength.toNat ≤ stride.toNat
  domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
    address.toNat < orderPos.toNat + capacity.toNat * 8 → state.memaddrs address
  cell0 : state.memory (table + 0) = .word keyLength
  cell8 : state.memory (table + 8) = .word stride
  cell16 : state.memory (table + 16) = .word capacity
  cell24 : state.memory (table + 24) = .word count
  cell32 : state.memory (table + 32) = .word keys
  cell40 : state.memory (table + 40) = .word values
  cell48 : state.memory (table + 48) = .word used
  cell56 : state.memory (table + 56) = .word order
  cell64 : state.memory (table + 64) = .word orderPos
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)
  room : count.toNat < capacity.toNat

/-- The existing 32-byte invariant is exactly the width-parameterized case. -/
theorem hashTableArraysInvariant_32_iff {F : Type}
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) :
    HashTableArraysInvariant 32 table keys stride capacity used values order orderPos count bits state ↔
    HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state := by
  constructor
  · intro invariant
    exact {
    code := invariant.code
    power := invariant.power
    keysAligned := invariant.keysAligned
    strideAligned := invariant.strideAligned
    valuesAligned := invariant.valuesAligned
    usedAligned := invariant.usedAligned
    orderAligned := invariant.orderAligned
    orderPosAligned := invariant.orderPosAligned
    headerKeys := invariant.headerKeys
    headerValues := invariant.headerValues
    keysBefore := invariant.keysBefore
    valuesBefore := invariant.valuesBefore
    usedBefore := invariant.usedBefore
    orderBefore := invariant.orderBefore
    endBound := invariant.endBound
    fits := invariant.fits
    domain := invariant.domain
    cell0 := invariant.cell0
    cell8 := invariant.cell8
    cell16 := invariant.cell16
    cell24 := invariant.cell24
    cell32 := invariant.cell32
    cell40 := invariant.cell40
    cell48 := invariant.cell48
    cell56 := invariant.cell56
    cell64 := invariant.cell64
    agreement := invariant.agreement
    room := invariant.room
    }
  · intro invariant
    exact {
    code := invariant.code
    power := invariant.power
    keysAligned := invariant.keysAligned
    strideAligned := invariant.strideAligned
    valuesAligned := invariant.valuesAligned
    usedAligned := invariant.usedAligned
    orderAligned := invariant.orderAligned
    orderPosAligned := invariant.orderPosAligned
    headerKeys := invariant.headerKeys
    headerValues := invariant.headerValues
    keysBefore := invariant.keysBefore
    valuesBefore := invariant.valuesBefore
    usedBefore := invariant.usedBefore
    orderBefore := invariant.orderBefore
    endBound := invariant.endBound
    fits := invariant.fits
    domain := invariant.domain
    cell0 := invariant.cell0
    cell8 := invariant.cell8
    cell16 := invariant.cell16
    cell24 := invariant.cell24
    cell32 := invariant.cell32
    cell40 := invariant.cell40
    cell48 := invariant.cell48
    cell56 := invariant.cell56
    cell64 := invariant.cell64
    agreement := invariant.agreement
    room := invariant.room
    }

#print axioms hashTableArraysInvariant_32_iff
end InitECandidate.Runtime

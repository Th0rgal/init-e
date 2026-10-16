import InitECandidate.Runtime.HashTableArraysInvariant32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Pure local and clock changes retain the relocated table invariant. -/
theorem HashTableArraysInvariant32.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post := by
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext index
    unfold hashOccupancyRead
    rw [memory,addresses,endian]
  exact {
    code := code.trans invariant.code
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
    domain := by rw [addresses]; exact invariant.domain
    cell0 := by rw [memory]; exact invariant.cell0
    cell8 := by rw [memory]; exact invariant.cell8
    cell16 := by rw [memory]; exact invariant.cell16
    cell24 := by rw [memory]; exact invariant.cell24
    cell32 := by rw [memory]; exact invariant.cell32
    cell40 := by rw [memory]; exact invariant.cell40
    cell48 := by rw [memory]; exact invariant.cell48
    cell56 := by rw [memory]; exact invariant.cell56
    cell64 := by rw [memory]; exact invariant.cell64
    agreement := by rw [reads]; exact invariant.agreement
    room := invariant.room
  }

#print axioms HashTableArraysInvariant32.after_read
end InitECandidate.Runtime

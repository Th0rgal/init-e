import InitECandidate.Runtime.HashTableArraysInvariant32
import InitECandidate.Runtime.HashTableInvariant32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Constructor-specific live facts establish the general relocated-array invariant. -/
theorem HashTableInvariant32.arrays {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state) :
    HashTableArraysInvariant32 table (allocationEnd table 72) (allocationEnd 0 32) capacity
      (htabNewUsed table 32 capacity) (htabNewValues table 32 capacity) (htabNewOrder table 32 capacity)
      (htabNewOrderPos table 32 capacity) count bits state := by
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := htabNew_insertion_layout table 32 capacity (by decide) invariant.heapBudget
  obtain ⟨ka,sa,fits,hk,ku⟩ := htabNew_key_layout table 32 capacity (by decide) invariant.heapBudget
  exact {
    code := invariant.code
    power := invariant.power
    keysAligned := ka
    strideAligned := sa
    valuesAligned := va
    usedAligned := ua
    orderAligned := oa
    orderPosAligned := ra
    headerKeys := hk
    headerValues := hv
    keysBefore := ku
    valuesBefore := vu
    usedBefore := uo
    orderBefore := orr
    endBound := limit
    fits := fits
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

#print axioms HashTableInvariant32.arrays
end InitECandidate.Runtime

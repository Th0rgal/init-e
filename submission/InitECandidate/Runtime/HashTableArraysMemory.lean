import InitECandidate.Runtime.HashTableArraysRead
import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.header_domain {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (offset : Nat) (small : offset ≤ 64) : state.memaddrs (table + BitVec.ofNat 64 offset) := by
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have limit := invariant.endBound
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  apply invariant.domain <;> omega

/-- Relocated table invariants discharge the shared insertion memory facts. -/
theorem HashTableArraysInvariant.insertion_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state) :
    HashInsertTableMemory capacity used table values order orderPos count state :=
  hashInsert_table_memory_from_layout capacity used table values order orderPos count state
    invariant.valuesAligned invariant.usedAligned invariant.orderAligned invariant.orderPosAligned invariant.headerValues
    invariant.valuesBefore invariant.usedBefore invariant.orderBefore invariant.endBound invariant.domain
    invariant.cell40 invariant.cell24 invariant.agreement invariant.room


#print axioms HashTableArraysInvariant.header_domain
#print axioms HashTableArraysInvariant.insertion_memory
end InitECandidate.Runtime

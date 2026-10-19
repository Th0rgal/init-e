import InitECandidate.Runtime.NodedbTableGetBound
import InitECandidate.Runtime.HashGetReturnedValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every present result from an actual built node table remains in its
witness registry. No alignment or readability assumption is made on the key. -/
theorem nodedb_table_get_returned_values {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table heap total key : BitVec 64) (targets : Set (BitVec 64))
    (built : NodedbTableAt s table heap total) (entries : HashTableValuesIn table targets s)
    (atTable : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "key") = some (.val (.word key))) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_get) =
      (some (.returned v),post)) :
    ∃ present value : BitVec 64, v = .rStruct [.val (.word present),.val (.word value)] ∧
      (present = 0 ∨ present = 1) ∧ (present ≠ 0 → value ∈ targets) := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,_,_,_,inv,_,_⟩ := built
  have valueDomain : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → s.memaddrs (values + slot * 8) := by
    intro slot inside
    have bound : values.toNat + capacity.toNat * 8 ≤ 33806089496 := by
      have a := inv.valuesBefore
      have b := inv.usedBefore
      have c := inv.orderBefore
      have d := inv.endBound
      omega
    have product : slot.toNat * 8 < 2 ^ 64 := by omega
    have sum : values.toNat + slot.toNat * 8 < 2 ^ 64 := by omega
    have address : (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
      change (values.toNat + (slot.toNat * 8 % 2 ^ 64)) % 2 ^ 64 = _
      rw [Nat.mod_eq_of_lt product,Nat.mod_eq_of_lt sum]
    apply inv.domain _
    · rw [address]
      have aligned := inv.valuesAligned
      omega
    · rw [address]
      have header := inv.headerValues
      omega
    · rw [address]
      have a := inv.valuesBefore
      have b := inv.usedBefore
      have c := inv.orderBefore
      omega
  exact hashGet_returned_values_in s post table key capacity used values bits targets inv.code inv.power atTable atKey
    (inv.header_domain 16 (by omega) (by omega)) inv.cell16
    (inv.header_domain 48 (by omega) (by omega)) inv.cell48
    (inv.header_domain 40 (by omega) (by omega)) inv.cell40 valueDomain entries v run

#print axioms nodedb_table_get_returned_values
end InitECandidate.Runtime

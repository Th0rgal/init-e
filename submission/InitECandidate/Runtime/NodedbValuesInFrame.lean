import InitECandidate.Runtime.NodedbValuesIn
import InitECandidate.Runtime.HtabMergeCore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Lookup-facing witness membership survives changes outside the actual table
allocation. The header and occupancy used by the predicate are read from memory. -/
theorem HashTableValuesIn.after_table_frame {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (post : PanSemStateFiniteExact 64 G)
    (targets : Set (BitVec 64))
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (entries : HashTableValuesIn table targets s)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be)
    (keep : ∀ w : BitVec 64, table.toNat ≤ w.toNat →
      w.toNat < orderPos.toNat + capacity.toNat * 8 → post.memory w = s.memory w) :
    HashTableValuesIn table targets post := by
  have cells := inv.toRegions.foot_keep (r := post) (by
    intro w foot
    have upper := inv.foot_below w.toNat foot
    have lower : table.toNat ≤ w.toNat := by
      have := inv.headerKeys
      have := inv.keysBefore
      have := inv.usedBefore
      have := inv.orderBefore
      unfold HtabFoot at foot
      omega
    exact keep w lower upper)
  intro otherCapacity otherUsed otherValues capCell usedCell valueCell
  have c16 : post.memory (table + 16) = s.memory (table + 16) := cells.1 16 (by decide)
  have c48 : post.memory (table + 48) = s.memory (table + 48) := cells.1 48 (by decide)
  have c40 : post.memory (table + 40) = s.memory (table + 40) := cells.1 40 (by decide)
  rw [c16] at capCell
  rw [c48] at usedCell
  rw [c40] at valueCell
  have capEq : otherCapacity = capacity := HolWordLab.word.inj (capCell.symm.trans inv.cell16)
  have usedEq : otherUsed = used := HolWordLab.word.inj (usedCell.symm.trans inv.cell48)
  have valuesEq : otherValues = values := HolWordLab.word.inj (valueCell.symm.trans inv.cell40)
  subst otherCapacity
  subst otherUsed
  subst otherValues
  intro q inside occupied value cell
  have occ := occupancyRead_congr_at post s used q (cells.2.1 q inside) domain endian
  have valueFrame : post.memory (values + q * 8) = s.memory (values + q * 8) := by
    apply keep
    · rw [(inv.toRegions.slot_toNat q inside).1]
      have := inv.headerValues
      omega
    · rw [(inv.toRegions.slot_toNat q inside).1]
      have := inv.valuesBefore
      have := inv.usedBefore
      have := inv.orderBefore
      omega
  exact entries capacity used values inv.cell16 inv.cell48 inv.cell40 q inside
    (by rw [← occ]; exact occupied) value (valueFrame.symm.trans cell)

#print axioms HashTableValuesIn.after_table_frame
end InitECandidate.Runtime

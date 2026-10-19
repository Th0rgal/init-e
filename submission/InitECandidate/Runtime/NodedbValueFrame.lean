import InitECandidate.Runtime.NodedbSetValues
import InitECandidate.Runtime.HtabMergeCore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Agreement over the real table allocation preserves its witness-value
membership, even when workspace memory outside that allocation changes. -/
theorem VTabs.after_table_frame {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (post : PanSemStateFiniteExact 64 G)
    (targets : Set (BitVec 64))
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (ordered : OrderInv s capacity count used order orderPos)
    (vt : VTabs targets s capacity count used keys stride values order)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be)
    (keep : ∀ w : BitVec 64, table.toNat ≤ w.toNat →
      w.toNat < orderPos.toNat + capacity.toNat * 8 → post.memory w = s.memory w) :
    VTabs targets post capacity count used keys stride values order := by
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
  have occ (q : BitVec 64) (inside : q.toNat < capacity.toNat) :
      hashOccupancyRead post used q = hashOccupancyRead s used q :=
    occupancyRead_congr_at post s used q (cells.2.1 q inside) domain endian
  refine ⟨?_,?_,vt.2.2⟩
  · intro k inside slot cell
    have capInside : k.toNat < capacity.toNat := lt_of_lt_of_le inside inv.toRegions.count_le
    have oldCell : s.memory (order + k * 8) = .word slot := (cells.2.2.1 k capInside).symm.trans cell
    obtain ⟨expected,expectedCell,expectedBound⟩ := ordered.2 k inside
    have same : expected = slot := HolWordLab.word.inj (expectedCell.symm.trans oldCell)
    have slotBound : slot.toNat < capacity.toNat := by simpa only [same] using expectedBound
    rw [occ slot slotBound]
    exact vt.1 k inside slot oldCell
  · intro q inside occupied value cell
    have valueCell : post.memory (values + q * 8) = s.memory (values + q * 8) := by
      apply keep
      · rw [(inv.toRegions.slot_toNat q inside).1]
        have := inv.headerValues
        omega
      · rw [(inv.toRegions.slot_toNat q inside).1]
        have := inv.valuesBefore
        have := inv.usedBefore
        have := inv.orderBefore
        omega
    exact vt.2.1 q inside (by rw [← occ q inside]; exact occupied) value (valueCell.symm.trans cell)

#print axioms VTabs.after_table_frame
end InitECandidate.Runtime

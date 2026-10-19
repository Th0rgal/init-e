import InitECandidate.Runtime.HtabMergeCore
import InitECandidate.Runtime.NodedbLoopInvariant
import InitECandidate.Runtime.NodedbWindowGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A later database build's protected-memory frame keeps an older table whose
arrays end below its entry heap and whose header is above the hash workspaces. -/
theorem nodedb_old_table_after_protected_frame {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (post : PanSemStateFiniteExact 64 G)
    (keyLength table keys stride capacity used values order orderPos count heap statePad pad output : BitVec 64)
    (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (ordered : OrderInv s capacity count used order orderPos)
    (extent : orderPos.toNat + capacity.toNat * 8 ≤ heap.toNat)
    (stateBelow : statePad.toNat + 200 ≤ table.toNat)
    (padBelow : pad.toNat + 136 ≤ table.toNat) (outputBelow : output.toNat + 32 ≤ table.toNat)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be) (code : post.code = s.code)
    (frame : ∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
      ¬ MWin pad 136 w → ¬ MWin output 32 w → post.memory w = s.memory w) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits post ∧
      OrderInv post capacity count used order orderPos := by
  have keep : ∀ w : BitVec 64, HtabFoot table capacity used order orderPos w.toNat →
      post.memory w = s.memory w := by
    intro w inside
    have upper := inv.foot_below w.toNat inside
    have lower : table.toNat ≤ w.toNat := by
      have := inv.headerKeys
      have := inv.keysBefore
      have := inv.usedBefore
      have := inv.orderBefore
      unfold HtabFoot at inside
      omega
    exact frame w (by omega) (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  have cells := inv.toRegions.foot_keep (r := post) keep
  exact ⟨inv.congr domain endian code cells.1 cells.2.1,
    ordered.congr inv.toRegions.count_le domain endian cells.2.1 cells.2.2.1 cells.2.2.2⟩

#print axioms nodedb_old_table_after_protected_frame
end InitECandidate.Runtime

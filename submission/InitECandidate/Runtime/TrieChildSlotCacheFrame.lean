import InitECandidate.Runtime.TrieChildSlotMetadataSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Cache invalidation's three-cell frame preserves previously prepared child
slot typing; its only value-dependent case is a positive extension length. -/
theorem TrieChildSlot.after_cache_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (layout : TrieNodeLayout live extensions branches size) (slot node : BitVec 64)
 (typed : TrieChildSlot s extensions branches slot) (member : node∈live) (capacity : 32≤size node)
 (frame : ∀watched : BitVec 64,watched≠node+8 →watched≠node+16 →watched≠node+24 →post.memory watched=s.memory watched) :
 TrieChildSlot post extensions branches slot := by
 apply typed.after_length_frame
 intro parent registered
 have separate (offset : Nat) (small : offset<32) : parent+BitVec.ofNat 64 40≠node+BitVec.ofNat 64 offset :=
  layout.fields_ne parent node (layout.extensionLive registered) member 40 offset
   (by have:=layout.extensionSize parent registered;omega) (by omega) (Or.inr (by omega))
 exact frame _ (separate 8 (by decide)) (separate 16 (by decide)) (separate 24 (by decide))
#print axioms TrieChildSlot.after_cache_frame
end InitECandidate.Runtime

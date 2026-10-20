import InitECandidate.Runtime.NormalRelGlobalCall
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- An aligned capped heap word stays aligned and capped and only grows.
Other globals may change according to the original source. -/
def HeapAdvance (before after : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
 ∀p : BitVec 64,before.lookup (ofString "heap_ptr")=some (.val (.word p))→p.toNat%8=0→p.toNat≤33806089496→
 ∃q : BitVec 64,after.lookup (ofString "heap_ptr")=some (.val (.word q)) ∧p.toNat≤q.toNat ∧q.toNat%8=0 ∧q.toNat≤33806089496

theorem heapAdvance_preorder : GlobalsPreorder HeapAdvance where
 refl := fun _ p h a c=>⟨p,h,le_refl _,a,c⟩
 trans := by
  intro a b c ab bc p h al cap
  obtain ⟨q,hq,pq,aq,cq⟩:=ab p h al cap
  obtain ⟨t,ht,qt,alignedT,ct⟩:=bc q hq aq cq
  exact ⟨t,ht,by omega,alignedT,ct⟩

theorem heapAdvance_update (name : MlS) (different : name≠ofString "heap_ptr")
 (a b : HolFiniteMapExact MlS (ValueHOL 64)) (v : ValueHOL 64) (rel : HeapAdvance a b) :
 HeapAdvance a (b.update (name,v)) := by
 intro p h al cap
 obtain ⟨q,hq,pq,aq,cq⟩:=rel p h al cap
 exact ⟨q,by simpa [HolFiniteMapExact.lookup_update,FUPDATE,different] using hq,pq,aq,cq⟩

theorem heapAdvance_leaf {program : ProgHOL 64}
 (supported : avoidsGlobalAssignment (ofString "heap_ptr") program=true) : NormalRel HeapAdvance program := by
 unfold NormalRel
 intro F s post result code run continuing
 have frame:=evaluate_avoidsGlobalAssignment (ofString "heap_ptr") program supported s
 rw [run] at frame
 intro p h al cap
 exact ⟨p,frame.trans h,le_refl _,al,cap⟩

theorem normalRel_heapAdvance_of_heapRel {program : ProgHOL 64} (rel : NormalRel HeapRel program) :
 NormalRel HeapAdvance program := by
 unfold NormalRel at *
 intro F s post result code run continuing
 exact (rel s post result code run continuing).2

theorem returnedRel_heapAdvance_of_heapRel {program : ProgHOL 64} (rel : ReturnedRel HeapRel program) :
 ReturnedRel HeapAdvance program := by
 unfold ReturnedRel at *
 intro F s post value code run
 exact (rel s post value code run).2
#print axioms heapAdvance_preorder
#print axioms heapAdvance_leaf
end InitECandidate.Runtime

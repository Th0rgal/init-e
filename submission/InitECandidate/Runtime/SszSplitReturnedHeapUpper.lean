import InitECandidate.Runtime.StatelessWitnessMemFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem sszSplitReturned_heap_upper {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length limit heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr")=some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat≤33806089496) (aligned : heapPointer.toNat%8=0)
    (returned : SszSplitVarListReturned state length limit heapPointer value post) :
    ∃ nextHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      heapPointer.toNat≤nextHeap.toNat ∧nextHeap.toNat≤33806089496 ∧nextHeap.toNat%8=0 ∧
      nextHeap.toNat≤heapPointer.toNat+4*length.toNat+7 ∧
      ∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=state.globals.lookup key := by
  rcases returned with ⟨_,_,globals⟩|⟨_,first,_,ok,_,_,request,globals⟩
  · refine ⟨heapPointer,by rw [globals];exact heap,le_refl _,heapBound,aligned,by omega,?_⟩
    intro key different;rw [globals]
  · let count:=first >>> (2 : Nat)
    have countBound : count.toNat≤length.toNat/4 := by
      have firstLe : first.toNat≤length.toNat := by have h:=ok.2.2;rw [BitVec.lt_def] at h;omega
      dsimp only [count]
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right firstLe
    have product : (count*16).toNat≤count.toNat*16 := by
      rw [BitVec.toNat_mul]
      exact Nat.mod_le _ _
    have sizeUpper : (count*16).toNat≤4*length.toNat := by
      have remainder:=Nat.mod_add_div length.toNat 4
      omega
    have sum:=allocationGuard_sum_bound heapPointer (count*16) heapBound request
    have cover:=allocationEnd_covers heapPointer (count*16) sum
    refine ⟨allocationEnd heapPointer (count*16),?_,by omega,allocationEnd_within_heap heapPointer _ heapBound request,cover.2.2,by omega,?_⟩
    · rw [globals];simp [count,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro key different
      rw [globals];simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 def HeapGrowUpper {F : Type} (heap length : BitVec 64) (state post : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ next : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    heap.toNat≤next.toNat ∧next.toNat≤33806089496 ∧next.toNat%8=0 ∧next.toNat≤heap.toNat+4*length.toNat+7 ∧
    ∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=state.globals.lookup key
#print axioms sszSplitReturned_heap_upper
end InitECandidate.Runtime

import InitECandidate.Runtime.NodedbSetValues
import InitECandidate.Runtime.NodedbConstructorReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual empty constructor establishes witness-pointer membership before
the insertion loop. No uninitialized value cell is treated as occupied. -/
theorem nodedb_constructor_values {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (pointer capacity array total : BitVec 64) (bits : Nat)
    (ready : NodedbTableReady s pointer capacity bits next) :
    ∃ keys stride used values order orderPos heap : BitVec 64,
      HtabAligned 32 pointer keys stride capacity used values order orderPos 0 bits next ∧
      OrderInv next capacity 0 used order orderPos ∧
      VTabs (NodedbSliceTargets array total) next capacity 0 used keys stride values order ∧
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      orderPos.toNat + capacity.toNat * 8 ≤ heap.toNat := by
  obtain ⟨_,_,_,_,_,_,_,keys,stride,used,values,order,orderPos,inv,separate,ordered,
    heap,atHeap,extent,_,_⟩ := ready
  have members := HashTableValuesIn.empty next pointer capacity used (NodedbSliceTargets array total)
    inv.cell16 inv.cell48 (by simpa using inv.agreement.symm)
  refine ⟨keys,stride,used,values,order,orderPos,heap,inv,ordered,?_,atHeap,extent⟩
  refine ⟨?_,?_,Or.inl separate⟩
  · intro k inside
    simp at inside
  · exact members capacity used values inv.cell16 inv.cell48 inv.cell40

#print axioms nodedb_constructor_values
end InitECandidate.Runtime

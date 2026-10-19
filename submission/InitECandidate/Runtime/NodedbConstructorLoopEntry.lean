import InitECandidate.Runtime.NodedbWindowGeometry
import InitECandidate.Runtime.NodedbSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The original constructor's real normal-result contract establishes the
initial loop invariant. Future slice words come from retained input memory. -/
theorem nodedb_constructor_loop_entry {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (pointer capacity total array statePad pad output : BitVec 64) (bits : Nat)
    (ready : NodedbTableReady s pointer capacity bits next)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712) (capacitySmall : capacity.toNat ≤ 536870912)
    (margin : 2 * total.toNat + 2 ≤ capacity.toNat) (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712) :
    ∃ c : NodedbLoopConfig, c.total = total ∧ c.capacity = capacity ∧ NodedbLoopGeometry c ∧
      ∃ heap : BitVec 64, NodedbLoopInv c 0 0 heap (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next) := by
  obtain ⟨tableLocal,locals,code,domain,endian,frame,rel,keys,stride,used,values,order,orderPos,inv,keysBefore,ordered,
    heap,heapGlobal,extent,heapAligned,heapInside⟩ := ready
  let c : NodedbLoopConfig := ⟨statePad,pad,array,total,output,pointer,keys,stride,capacity,used,values,order,orderPos,bits⟩
  have geometry : NodedbLoopGeometry c := nodedb_geometry_of_intervals c next 0 inv small capacitySmall margin
    outputAligned arrayEnd stateEnd padEnd outputEnd
  have headerBelow : pointer.toNat + 72 ≤ heap.toNat := by
    have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
    omega
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0#64))) next
  have keep (key : MlS) (different : key ≠ ofString "i") : entered.locals.lookup key = next.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨c,rfl,rfl,geometry,heap,?_,?_,?_,?_,?_,?_,?_,heapGlobal,heapAligned,headerBelow,heapInside,?_,?_,
    inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atTotal
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atArray
  · exact (keep _ (by decide)).trans tableLocal
  · exact (rel.1 _ (by decide)).trans atState
  · exact (rel.1 _ (by decide)).trans atPad
  · exact (rel.1 _ (by decide)).trans atOutput
  · simp
  · simp
  · intro a h1 h2 h3
    change next.memaddrs a
    rw [domain]; exact arena a h1 h2 h3
  · intro j inside
    obtain ⟨src,len,sd,ld,sc,lc,sizeSmall⟩ := slices j inside
    obtain ⟨p,l⟩ := geometry.sliceProtected j inside
    refine ⟨src,len,?_,?_,?_,?_,sizeSmall⟩
    · change next.memaddrs _; rw [domain]; exact sd
    · change next.memaddrs _; rw [domain]; exact ld
    · exact (frame _ p.1).trans sc
    · exact (frame _ l.1).trans lc

#print axioms nodedb_constructor_loop_entry
end InitECandidate.Runtime

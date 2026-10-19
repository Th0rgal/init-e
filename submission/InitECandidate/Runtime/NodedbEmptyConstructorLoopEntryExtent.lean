import InitECandidate.Runtime.NodedbEmptyConstructorLoopEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_empty_constructor_loop_entry_extent {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (pointer capacity total array statePad pad output : BitVec 64) (bits : Nat)
    (ready : NodedbTableReady s pointer capacity bits next)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (empty : total = 0)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a) :
    ∃ c : NodedbLoopConfig, c.total = 0 ∧ c.capacity = capacity ∧ c.table = pointer ∧
      c.pointer = statePad ∧ c.pad = pad ∧ c.array = array ∧ c.output = output ∧
      ∃ heap : BitVec 64, c.orderPos.toNat + c.capacity.toNat * 8 ≤ heap.toNat ∧ NodedbLoopInv c 0 0 heap
        (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next) := by
  subst empty
  obtain ⟨tableLocal,locals,code,domain,endian,frame,rel,keys,stride,used,values,order,orderPos,inv,keysBefore,
    ordered,heap,heapGlobal,extent,heapAligned,heapInside⟩ := ready
  let c : NodedbLoopConfig :=
    ⟨statePad,pad,array,0,output,pointer,keys,stride,capacity,used,values,order,orderPos,bits⟩
  have keep (key : MlS) (different : key ≠ ofString "i") :
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next).locals.lookup key =
        next.locals.lookup key := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨c,rfl,rfl,rfl,rfl,rfl,rfl,rfl,heap,extent,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atTotal
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atArray
  · exact (keep _ (by decide)).trans tableLocal
  · exact (rel.1 _ (by decide)).trans atState
  · exact (rel.1 _ (by decide)).trans atPad
  · exact (rel.1 _ (by decide)).trans atOutput
  · exact heapGlobal
  · exact heapAligned
  · have headerKeys := inv.headerKeys
    have keysBefore' := keysBefore
    have valuesBefore := inv.valuesBefore
    have usedBefore := inv.usedBefore
    have orderBefore := inv.orderBefore
    show pointer.toNat + 72 ≤ heap.toNat
    omega
  · exact heapInside
  · simp [c]
  · simp
  · exact inv.transfer rfl rfl rfl rfl
  · exact ordered.transfer rfl rfl rfl
  · intro a h1 h2 h3
    change next.memaddrs a
    rw [domain]
    exact arena a h1 h2 h3
  · intro j inside
    exact absurd inside (by simp [c])

#print axioms nodedb_empty_constructor_loop_entry_extent
end InitECandidate.Runtime

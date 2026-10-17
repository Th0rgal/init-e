import InitECandidate.Runtime.RollbackWorld
import InitECandidate.Runtime.HashTableDeleteCallPhysicalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Lift the actual deletion call's two-table preservation theorem to a fixed
registry. The separation premise accounts for the concrete array allocations. -/
theorem rollback_delete_physical_table_family {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (tableArgument keyArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat * 57 + 3 ≤ state.clock)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∀ other ∈ tables, RollbackTableReady widths other post) ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock := by
  obtain ⟨post,run,⟨remaining,_,target⟩,cost,clock,_⟩ := ready.delete_call_supported state (widths table) table pointer keys stride capacity used values order orderPos items key bits supported
    tableArgument keyArgument args keyAligned words bytes budget
  refine ⟨post,run,?_,cost,clock⟩
  intro other member
  by_cases same : other = table
  · subst other
    exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,remaining,bits,target,strideBound,large⟩
  · obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,otherReady,otherStride,otherLarge⟩ := family other member
    have frontier : op = pointer := by
      have equal := otherReady.live.frontier.heap.symm.trans ready.live.frontier.heap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    have separation := separated other member same op ok os oc ou ov oo oop oi ob otherReady
    subst op
    obtain ⟨checked,checkedRun,_,preserved,_⟩ := ready.delete_call_supported_with_physical_table state (widths table) table pointer keys stride capacity used values order orderPos items key bits supported
      tableArgument keyArgument args keyAligned words bytes budget
      (widths other) other ok os oc ou ov oo oop oi ob otherReady separation
    have identical : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
    rw [identical]
    exact ⟨pointer,ok,os,oc,ou,ov,oo,oop,oi,ob,preserved,otherStride,otherLarge⟩

#print axioms rollback_delete_physical_table_family
end InitECandidate.Runtime

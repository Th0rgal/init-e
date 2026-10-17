import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.HashTableSetCallPhysicalSupported
import InitECandidate.Runtime.HashTableReadySetCallSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful set preserves the fixed table registry under separation of live
physical regions, allowing previously relocated arrays and interleaved headers. -/
theorem rollback_set_other_physical_footprints {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (budget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      (∀ other ∈ tables, other ≠ table → ∀ address, rollbackTableFootprint widths other post address → rollbackTableFootprint widths other state address) := by
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    rfl
  obtain ⟨post,run,target,_⟩ := ready.set_call_supported_safe_plan state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
    strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan (by omega)
    ready.live.frontier.heap domain tableArgument keyArgument valueArgument args large keyAligned words bytes
  refine ⟨post,run,?_⟩
  intro other member different address inside
  obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,otherReady,otherStride,otherLarge⟩ := family other member
  have frontier : op = pointer := by
    have equal := otherReady.live.frontier.heap.symm.trans ready.live.frontier.heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have separation := separated other member different op ok os oc ou ov oo oop oi ob otherReady
  subst op
  obtain ⟨checked,checkedRun,cases,_⟩ := ready.set_call_supported_with_physical_table_safe_plan state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
    strideBound safePlan budget domain large keyAligned words bytes
    (widths other) other ok os oc ou ov oo oop oi ob otherReady separation tableArgument keyArgument valueArgument args
  have identical : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [identical] at inside
  rcases cases with original | grown
  · obtain ⟨_,_,_,preserved⟩ := original
    exact (otherReady.rollback_footprint_iff state widths other pointer ok os oc ou ov oo oop oi ob address).mpr
      ((preserved.rollback_footprint_iff checked widths other pointer ok os oc ou ov oo oop oi ob address).mp inside)
  · exact (otherReady.rollback_footprint_iff state widths other pointer ok os oc ou ov oo oop oi ob address).mpr
      ((grown.2.rollback_footprint_iff checked widths other _ ok os oc ou ov oo oop oi ob address).mp inside)
#print axioms rollback_set_other_physical_footprints
end InitECandidate.Runtime

import InitECandidate.Runtime.HashTableDeleteCallOtherValuesIn
import InitECandidate.Runtime.HashTableDeleteCallValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredSet
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual deletion calls preserve registered values throughout the watched table family. -/
theorem RollbackWorld.registered_delete_values_in_family {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 43 ≤ state.clock)
    (tableArgument keyArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
 :
    ∀ other ∈ watched, HashTableValuesIn other targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_del") [tableArgument,keyArgument])).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have budget : capacity.toNat * 57 + 3 ≤ state.clock := by omega
  intro other belongs
  by_cases same : other = table
  · subst other
    obtain ⟨post,run,_,postRegistered,_⟩ := ready.delete_call_values_in state (widths table) table pointer keys stride capacity used values order reverse items key bits supported
      tableArgument keyArgument args aligned words bytes budget targets (registered table belongs)
    rw [run]
    exact postRegistered
  · obtain ⟨op,ok,os,oc,ou,ov,oo,orev,oi,ob,otherReady,_,_⟩ := world.ready other (watchedSubset belongs)
    have frontier : op = pointer := by
      have equal := otherReady.live.frontier.heap.symm.trans ready.live.frontier.heap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    subst op
    have apart : ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order reverse address →
        ¬tablePhysicalRegion other ok os oc ou ov oo orev address := by
      intro address targetMember otherMember
      exact separated table member other (watchedSubset belongs) (Ne.symm same) address
        ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order reverse items bits address).mpr targetMember)
        ((otherReady.rollback_footprint_iff state widths other pointer ok os oc ou ov oo orev oi ob address).mpr otherMember)
    obtain ⟨post,run,_,_,postRegistered,_⟩ := ready.delete_call_other_values_in state (widths table) table pointer keys stride capacity used values order reverse items key bits supported
      tableArgument keyArgument args aligned words bytes budget
      (widths other) other ok os oc ou ov oo orev oi ob otherReady targets (registered other belongs) apart
    rw [run]
    exact postRegistered

#print axioms RollbackWorld.registered_delete_values_in_family
end InitECandidate.Runtime

import InitECandidate.Runtime.HashTableSetCallSavedValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredSet
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem RollbackWorld.registered_set_saved_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (journalBefore : journal.toNat + count.toNat * 32 ≤ table.toNat)
    (journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496)
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    JournalSavedValuesIn journal count.toNat watched targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
    have := ready.live.arrays.headerKeys
    have := ready.live.arrays.keysBefore
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.frontier.allocated
    omega
  have domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) →
      ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
    intro safePlan address lower upper
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride small ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
    exact heapDomain address (by omega)
  exact ready.set_call_saved_values_in state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
    small ticks domain tableArgument keyArgument valueArgument args large aligned words bytes journal count.toNat watched targets saved journalBefore journalBound success

#print axioms RollbackWorld.registered_set_saved_values_in
end InitECandidate.Runtime

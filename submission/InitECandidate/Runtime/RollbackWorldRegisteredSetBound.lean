import InitECandidate.Runtime.RollbackWorldRegisteredSet
import InitECandidate.Runtime.HashTableReadySetCallAllPlansSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform cost of a registered table set, including unsafe allocation plans. -/
theorem RollbackWorld.registered_set_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 72 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have ceiling := hashSetRegistryCost_le_ceiling capacity (widths table) items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
  have callBudget : 2 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ 2 ^ 72 := by
    unfold hashSetRegistryCost at ceiling
    omega
  have bounded := ready.set_call_supported_all_plans_bounded state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
    small ready.live.frontier.aligned ready.live.frontier.bounded capacityBound (by omega) ready.live.frontier.heap
    (by intro address lower upper; exact heapDomain address upper) tableArgument keyArgument valueArgument args large aligned words bytes
  exact ⟨by omega,bounded.2⟩

#print axioms RollbackWorld.registered_set_bounded
end InitECandidate.Runtime

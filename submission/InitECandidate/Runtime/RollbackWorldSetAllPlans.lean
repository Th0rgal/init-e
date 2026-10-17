import InitECandidate.Runtime.RollbackWorldSetNoGrowthCall
import InitECandidate.Runtime.RollbackWorldSetUnsafeGrowthCall
import InitECandidate.Runtime.RollbackWorldSetSeparated
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every allocation plan either preserves the separated rollback world on
successful set or exits terminally without timeout. -/
theorem RollbackWorld.set_call_all_plans {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (budget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : RollbackPhysicalSeparated widths tables state) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post) ∨
    ((evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ none ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 2 * capacity.toNat + 10 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock) := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨post,run,valid,apart,_,_⟩ := RollbackWorld.set_call_no_growth_preserves state widths tables
      table pointer keys stride capacity used values order orderPos items key value bits supported ready
      keyAligned words bytes below (by omega) tableArgument keyArgument valueArgument args
      journal snapshot count world registered separated strideBound large
    exact Or.inl ⟨post,run,valid,apart⟩
  · by_cases safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
    · exact Or.inl (RollbackWorld.set_call_preserves_separation state widths tables
        table pointer keys stride capacity used values order orderPos items key value bits supported ready strideBound large
        safePlan budget domain tableArgument keyArgument valueArgument args keyAligned words bytes
        journal snapshot count world registered separated)
    · have outcome := RollbackWorld.set_unsafe_growth_call_dichotomy state widths tables
        table pointer keys stride capacity used values order orderPos items key value bits supported ready
        tableArgument keyArgument valueArgument args keyAligned words bytes (by omega)
        ready.live.frontier.heap ready.live.frontier.bounded safePlan (by omega)
        journal snapshot count world registered separated strideBound large
      rcases outcome with success | failure
      · obtain ⟨post,run,valid,apart,_,_⟩ := success
        exact Or.inl ⟨post,run,valid,apart⟩
      · exact Or.inr failure

#print axioms RollbackWorld.set_call_all_plans
end InitECandidate.Runtime

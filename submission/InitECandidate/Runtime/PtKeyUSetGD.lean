import InitECandidate.Runtime.HashTableValuesInSetCallAllPlansKU
/-!
The actual `htab_set` call on a ready table for a key of ANY alignment (`set_call_all_plans_values_inAny`): root's
contract without its `keyAligned` premise, needing instead that the key fits below the heap bound.  Aligned keys use
root's word fast paths; other keys use the byte-path (`KU`) chain.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_all_plans_values_inAny {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 2 ^ 74 ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) ∨
    ((evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ none ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 2 ^ 74 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock) := by
  by_cases al : key.toNat % 8 = 0
  · exact initialReady.set_call_all_plans_values_in state keyLength table pointer keys stride capacity used values order orderPos
      items key value bits supported targets registered member strideBound ticks domain tableArgument keyArgument valueArgument
      arguments capacityLarge al sourceWordDomain sourceByteDomain
  · have len8 : 8 ≤ keyLength.toNat := by rcases supported with rfl | rfl | rfl <;> decide
    exact initialReady.set_call_all_plans_values_inKU state keyLength table pointer keys stride capacity used values order orderPos
      items key value bits supported targets registered member strideBound ticks domain tableArgument keyArgument valueArgument
      arguments capacityLarge al len8 keyFit sourceWordDomain sourceByteDomain

#print axioms HashTableReady.set_call_all_plans_values_inAny
end InitECandidate.Runtime

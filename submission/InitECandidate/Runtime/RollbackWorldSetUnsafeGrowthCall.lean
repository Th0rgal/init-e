import InitECandidate.Runtime.RollbackWorldPhysicalUpdate
import InitECandidate.Runtime.HashTableReadySetUnsafeGrowthCallFrameDichotomy
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Above-threshold unsafe set either retains the complete separated world or
exits terminally without timeout; no safe-plan premise is needed. -/
theorem RollbackWorld.set_unsafe_growth_call_dichotomy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : (widths table) = 20 ∨ (widths table) = 32 ∨ (widths table) = 52)
    (invariant : HashTableReady (widths table) table keys stride capacity used values order orderPos count bits pointer state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 10 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2)
    (journal snapshot countWorld : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot countWorld state)
    (registered : table ∈ tables) (separated : RollbackPhysicalSeparated widths tables state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot countWorld post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 10 ∧ post.clock ≤ state.clock) ∨
    ((evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ none ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 2 * capacity.toNat + 10 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock) := by
  have outcome := invariant.set_unsafe_growth_call_frame_dichotomy state (widths table) table pointer keys stride capacity used values order orderPos count key value bits supported
    tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes budget heap pointerBound notSafe loadFactor
  rcases outcome with success | failure
  · obtain ⟨post,run,updated,locals,globals,code,domain,endian,cost,remaining,frame⟩ := success
    have retained := world.after_physical_update separated table pointer keys stride capacity used values order orderPos count count bits
      registered invariant updated strideBound large frame locals globals code domain endian
    exact Or.inl ⟨post,run,retained.1,retained.2,cost,remaining⟩
  · exact Or.inr failure

#print axioms RollbackWorld.set_unsafe_growth_call_dichotomy
end InitECandidate.Runtime

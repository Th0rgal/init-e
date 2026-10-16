import InitECandidate.Runtime.HashTableLive32
import InitECandidate.Runtime.HashTableSetCallWithGrowthFrontier32
import InitECandidate.Runtime.HashTableSetUniformBound32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableLive32.set_call_safe_plan {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (live : HashTableLive32 table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableLive32 table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableLive32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have capacityBound := live.arrays.capacity_bounded state table keys stride capacity used values order orderPos items bits
  obtain ⟨post,run,cases,cost,remaining,locals,code,addresses,endian⟩ :=
    live.arrays.set_call_with_growth_frontier state table pointer keys stride capacity used values order orderPos items key value bits
      live.entries live.frontier.allocated strideBound live.frontier.aligned live.frontier.bounded capacityBound
      safePlan ticks live.frontier.heap domain tableArgument keyArgument valueArgument arguments capacityLarge keyAligned sourceWordDomain sourceByteDomain
  refine ⟨post,run,?_,cost,remaining,locals,code,addresses,endian⟩
  rcases cases with unchanged | grown
  · obtain ⟨nextCount,counts,arrays,entries,frontier⟩ := unchanged
    exact Or.inl ⟨nextCount,counts,⟨arrays,entries,frontier⟩⟩
  · obtain ⟨arrays,entries,frontier⟩ := grown
    exact Or.inr ⟨arrays,entries,frontier⟩

#print axioms HashTableLive32.set_call_safe_plan
end InitECandidate.Runtime

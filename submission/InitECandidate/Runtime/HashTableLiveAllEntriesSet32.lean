import InitECandidate.Runtime.HashTableLiveOrderedSet32
import InitECandidate.Runtime.HashTableSetCallWithGrowthAllEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableLive32.set_call_all_entries_safe_plan {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (live : HashTableLive32 table keys stride capacity used values order orderPos items bits pointer state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity items state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
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
        HashTableLive32 table keys stride capacity used values order orderPos nextCount bits pointer post ∧
        keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat ∧
        HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity nextCount post) ∨
       HashTableLive32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        pointer.toNat + (capacity * 2).toNat * stride.toNat ≤ (htabGrowValues pointer capacity stride).toNat ∧
        HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
        HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have capacityBound := live.arrays.capacity_bounded state table keys stride capacity used values order orderPos items bits
  obtain ⟨post,run,cases,cost,remaining,locals,code,addresses,endian⟩ :=
    live.set_call_ordered_safe_plan state table pointer keys stride capacity used values order orderPos items key value bits
      keysBeforeValues strideBound safePlan ticks domain tableArgument keyArgument valueArgument arguments capacityLarge keyAligned sourceWordDomain sourceByteDomain
  obtain ⟨checked,checkedRun,entryCases,_⟩ := live.arrays.set_call_with_growth_safe_plan_all_entries state
    table pointer keys stride capacity used values order orderPos items key value bits live.entries valueEntries reverseEntries keysBeforeValues
    live.frontier.allocated strideBound live.frontier.aligned live.frontier.bounded capacityBound safePlan ticks live.frontier.heap domain
    tableArgument keyArgument valueArgument arguments capacityLarge keyAligned sourceWordDomain sourceByteDomain
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at entryCases
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have distinct : capacity ≠ capacity * 2 := by
    intro eq
    have natural := congrArg BitVec.toNat eq
    rw [doubled] at natural
    omega
  refine ⟨post,run,?_,cost,remaining,locals,code,addresses,endian⟩
  rcases cases with unchanged | grown
  · obtain ⟨nextCount,counts,postLive,ordering⟩ := unchanged
    rcases entryCases with oldEntries | newEntries
    · obtain ⟨otherCount,_,otherArrays,_,words,reverse⟩ := oldEntries
      have countEq : nextCount = otherCount := by
        have cells := postLive.arrays.cell24.symm.trans otherArrays.cell24
        injection cells
      rw [← countEq] at reverse
      exact Or.inl ⟨nextCount,counts,postLive,ordering,words,reverse⟩
    · obtain ⟨otherArrays,_⟩ := newEntries
      have cells := postLive.arrays.cell16.symm.trans otherArrays.cell16
      have eq : capacity = capacity * 2 := by injection cells
      exact False.elim (distinct eq)
  · obtain ⟨postLive,ordering⟩ := grown
    rcases entryCases with oldEntries | newEntries
    · obtain ⟨_,_,otherArrays,_⟩ := oldEntries
      have cells := otherArrays.cell16.symm.trans postLive.arrays.cell16
      have eq : capacity = capacity * 2 := by injection cells
      exact False.elim (distinct eq)
    · obtain ⟨_,_,words,reverse⟩ := newEntries
      exact Or.inr ⟨postLive,ordering,words,reverse⟩

#print axioms HashTableLive32.set_call_all_entries_safe_plan
end InitECandidate.Runtime

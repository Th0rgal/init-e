import InitECandidate.Runtime.HashTableSetAboveOther32
import InitECandidate.Runtime.HashTableSetNoGrowthOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original set body preserving two ready tables, including growth. -/
theorem HashTableReady32.set_with_other_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 3 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits pointer post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨ (HashTableReady32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨nextCount,post,counts,run,valid,otherValid,cost,remaining,_,code,domain,endian⟩ :=
      ready.set_no_growth_with_earlier_table state table pointer keys stride capacity used values order orderPos items key value bits
        t k v keyAligned sourceWordDomain sourceByteDomain below (by omega)
        otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        otherReady beforeKeys beforeValues separate
    exact ⟨post,run,Or.inl ⟨nextCount,counts,valid,otherValid⟩,by omega,remaining,code,domain,endian⟩
  · obtain ⟨post,run,cases,cost,remaining,code,domain,endian⟩ :=
      ready.set_above_with_other state table pointer keys stride capacity used values order orderPos items key value bits
        t k v strideBound safePlan (by omega) domain (by omega) capacityLarge keyAligned sourceWordDomain sourceByteDomain
        otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separate beforeValues
    refine ⟨post,run,?_,by omega,remaining,code,domain,endian⟩
    rcases cases with unchanged | grown
    · exact Or.inl ⟨items,Or.inl rfl,unchanged⟩
    · exact Or.inr grown

#print axioms HashTableReady32.set_with_other_safe_plan
end InitECandidate.Runtime

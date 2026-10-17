import InitECandidate.Runtime.HashTableReadySetAboveThresholdRecordFrameSupported
import InitECandidate.Runtime.HashTableSetNoGrowthRecordFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_body_supported_record_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initial : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal : BitVec 64) (journalCount : Nat)
    (journalBefore : journal.toNat + journalCount * 32 ≤ pointer.toNat)
    (beforeKeys : journal.toNat + journalCount * 32 ≤ keys.toNat)
    (beforeValues : journal.toNat + journalCount * 32 ≤ values.toNat)
    (separateHeader : journal.toNat + journalCount * 32 ≤ table.toNat ∨ table.toNat + 72 ≤ journal.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
      rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
      change capacity.toNat * 2 = 2 * capacity.toNat
      omega
    obtain ⟨nextCount,post,counts,run,postReady,journalPost,cost,remaining,_,code,addresses,endian⟩ :=
      initial.set_no_growth_supported_with_record_frame state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega) journal journalCount (by omega) beforeKeys beforeValues separateHeader
    exact ⟨post,run,Or.inl ⟨nextCount,counts,postReady⟩,by rw [doubled]; omega,remaining,code,addresses,endian,journalPost⟩
  · obtain ⟨post,run,cases,cost,remaining,code,addresses,endian,journalPost⟩ := initial.set_above_threshold_record_frame_supported state
      keyLength table pointer keys stride capacity used values order orderPos items key value bits supported strideBound pointerAligned
      pointerBound capacityBound safePlan ticks heap domain tableLocal keyLocal valueLocal (by omega) capacityLarge keyAligned sourceWordDomain sourceByteDomain journal journalCount journalBefore beforeValues separateHeader
    refine ⟨post,run,?_,cost,remaining,code,addresses,endian,journalPost⟩
    rcases cases with unchanged | grown
    · exact Or.inl ⟨items,Or.inl rfl,unchanged⟩
    · exact Or.inr grown

#print axioms HashTableReady.set_body_supported_record_frame
end InitECandidate.Runtime

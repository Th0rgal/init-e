import InitECandidate.Runtime.HashTableSetLookupGrowthRecordFrameSupported
import InitECandidate.Runtime.HashTableSetLookupLinkedRecordFrameSupported
import InitECandidate.Runtime.DeclarationResultUnique
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_above_threshold_record_frame_supported {F : Type}
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
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal : BitVec 64) (journalCount : Nat)
    (journalBefore : journal.toNat + journalCount * 32 ≤ pointer.toNat)
    (beforeValues : journal.toNat + journalCount * 32 ≤ values.toNat)
    (separateHeader : journal.toNat + journalCount * 32 ≤ table.toNat ∨ table.toNat + 72 ≤ journal.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) := by
  obtain ⟨found,ready,inside,decl,growth⟩ := initial.live.arrays.set_lookup_growth_supported_record_frame state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    initial.live.entries initial.live.frontier.allocated strideBound pointerAligned pointerBound capacityBound safePlan ticks heap domain tableLocal keyLocal valueLocal loadFactor capacityLarge keyAligned sourceWordDomain sourceByteDomain journal journalCount journalBefore separateHeader
  obtain ⟨existing,other,_,_,otherDecl,present⟩ := initial.live.arrays.set_lookup_supported_linked_record_frame state keyLength table keys stride capacity used values order orderPos items key value bits supported
    tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain (by omega) initial.live.entries initial.valuesWord initial.reverse initial.linked journal journalCount (by omega) (Or.inr beforeValues)
  have equal := declaration_word_result_unique state ready other (ofString "i") (ofString "htab_find_slot")
    [.var .local (ofString "t"),.var .local (ofString "key")] found existing decl otherDecl
  by_cases missing : found = capacity
  · obtain ⟨post,run,postReady,cost,remaining,code,addresses,endian,journalPost⟩ := growth missing
    exact ⟨post,run,Or.inr postReady,cost,remaining,code,addresses,endian,journalPost⟩
  · have different : existing ≠ capacity := by rw [← equal]; exact missing
    obtain ⟨post,run,valid,orderValid,words,reverse,postLinked,cost,remaining,globals,code,addresses,endian,journalPost⟩ := present different
    exact ⟨post,run,Or.inl ⟨⟨valid,orderValid,initial.live.frontier.after_globals state post orderPos capacity pointer globals⟩,words,reverse,postLinked,initial.ordering⟩,by omega,remaining,code,addresses,endian,journalPost⟩

#print axioms HashTableReady.set_above_threshold_record_frame_supported
end InitECandidate.Runtime

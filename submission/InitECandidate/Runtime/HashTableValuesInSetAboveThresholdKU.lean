import InitECandidate.Runtime.HashTableValuesInSetAboveThreshold
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesWidthKU
import InitECandidate.Runtime.HashInsertProbeEntriesWidthKU
import InitECandidate.Runtime.HashInsertIndexEntriesWidthKU
import InitECandidate.Runtime.HashInsertHashAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertBodyAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
import InitECandidate.Runtime.HashInsertIndexLinkedWidthKU
import InitECandidate.Runtime.HashInsertHashLinkedSupportedKU
import InitECandidate.Runtime.HashInsertBodyLinkedSupportedKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCallLinkedSupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
import InitECandidate.Runtime.HashTableArraysFrameSupportedKU
import InitECandidate.Runtime.HashTableArraysAllEntriesSupportedKU
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertPhysicalFrameSupportedKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
import InitECandidate.Runtime.HashTableValuesInInsertCallKU
import InitECandidate.Runtime.HashTableValuesInReadyUpdatesKU
import InitECandidate.Runtime.HashTableValuesInSetMissingGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetGrowthKU
/-! Unaligned-key copy of `HashTableValuesInSetAboveThreshold` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_above_threshold_values_inKU {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have invariant := initialReady.live.arrays
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find_supportedKU state keyLength table keys stride capacity used values order orderPos items key bits supported _ _ arguments keyAligned len8 keyFit sourceWordDomain sourceByteDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry := valid.after_read ready entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have entryReady := initialReady.after_read state entered keyLength table keys stride capacity used values order orderPos items bits pointer memory globals code addresses endian
  have entryRegistered := registered.after_read memory addresses endian
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have domainEntry : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → entered.memaddrs address := by
    change ∀ address : BitVec 64, _ → _ → ready.memaddrs address
    rw [addresses]; exact domain
  have words : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceWordDomain
  have bytes : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceByteDomain
  by_cases same : found = capacity
  ·
    have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
    have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
      (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) validEntry.cell16
    obtain ⟨post,tail,postReady,postRegistered,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩ :=
      entryReady.set_missing_growth_values_inKU entered keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        t k v strideBound safePlan
        (by change 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ ready.clock; omega)
        domainEntry loadFactor capacityLarge keyAligned len8 keyFit words bytes targets entryRegistered member
    have bodyTail := selected.trans tail
    rw [source_hashSet_existing,decl,bodyTail]
    refine ⟨_,rfl,Or.inr (HashTableReady.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
        (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) postReady rfl rfl rfl rfl rfl),
      postRegistered.after_read rfl rfl rfl,?_,?_,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
    · change state.clock ≤ post.clock + 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
      change ready.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) at tailCost
      omega
    · change post.clock ≤ state.clock
      change post.clock ≤ ready.clock at tailRemaining
      omega

  · have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have strict : found.toNat < capacity.toNat := by
      have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      omega
    obtain ⟨post,run,valid,postRegistered,_,clock,_,postCode,postAddresses,postEndian⟩ :=
      entryReady.set_existing_values_in_frame entered keyLength table pointer keys stride capacity used values order orderPos items found value bits
        t i v strict hashSetMissing targets entryRegistered member
    rw [source_hashSet_existing,decl,run]
    refine ⟨_,rfl,Or.inl (valid.after_read post _ keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl),
      postRegistered.after_read rfl rfl rfl,?_,?_,postCode.trans code,postAddresses.trans addresses,postEndian.trans endian⟩
    · change state.clock ≤ post.clock + 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
      change post.clock = ready.clock at clock
      omega
    · change post.clock ≤ state.clock
      change post.clock = ready.clock at clock
      omega

#print axioms HashTableReady.set_above_threshold_values_inKU
end InitECandidate.Runtime

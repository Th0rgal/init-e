import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
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
import InitECandidate.Runtime.HashTableValuesInSetMissingKU
/-! Unaligned-key copy of `HashTableValuesInSetNoGrowth` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original no-growth set body retains registered-pointer membership
for both existing and missing keys, including actual lookup and scope exit. -/
theorem HashTableReady.set_no_growth_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 55 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets)
 :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
        post.memory address = state.memory address) ∧
      state.clock ≤ post.clock + 55 * capacity.toNat + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,lookupState,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    ready.live.arrays.find_supportedKU state keyLength table keys stride capacity used values order orderPos count key bits supported _ _ arguments keyAligned len8 keyFit sourceWordDomain sourceByteDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) lookupState
  have validEntry : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read lookupState entered keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := ready.after_read state entered keyLength table keys stride capacity used values order orderPos count bits pointer memory globals code addresses endian
  have enteredRegistered := entries.after_read memory addresses endian
  have branch : ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
        post.memory address = entered.memory address) ∧
      entered.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ entered.clock ∧
      post.globals = entered.globals ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
      have words : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
        change ∀ offset : Nat, _ → lookupState.memaddrs _
        rw [addresses]; exact sourceWordDomain
      have bytes : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
        change ∀ offset : Nat, _ → lookupState.memaddrs _
        rw [addresses]; exact sourceByteDomain
      obtain ⟨post,run,valid,registered,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_missing_values_in_no_growthKU entered keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
          t k v keyAligned len8 keyFit words bytes loadFactor (by change capacity.toNat + keyLength.toNat + 3 ≤ lookupState.clock; omega) targets enteredRegistered member
      exact ⟨count + 1,post,Or.inr rfl,selected.trans run,valid,registered,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,valid,registered,otherValid,clock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_existing_values_in_frame entered keyLength table pointer keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing targets enteredRegistered member
      exact ⟨count,post,Or.inl rfl,run,valid,registered,otherValid,by omega,by omega,tailGlobals,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨nextCount,post,counts,tail,postReady,postRegistered,postOther,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨nextCount,_,counts,rfl,
    postReady.after_read post _ keyLength table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl,
    postRegistered.after_read rfl rfl rfl,(by
      intro address outside
      exact (postOther address outside).trans (congrFun memory _)),
    ?_,?_,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · change state.clock ≤ post.clock + 55 * capacity.toNat + keyLength.toNat + 5
    change lookupState.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ lookupState.clock at tailRemaining
    omega

#print axioms HashTableReady.set_no_growth_values_inKU
end InitECandidate.Runtime

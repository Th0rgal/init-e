import InitECandidate.Runtime.HashTableValuesInSetUnsafe
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
import InitECandidate.Runtime.HashTableSetLookupFailureTerminalSupportedNoTimeoutKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
import InitECandidate.Runtime.HashTableValuesInInsertCallKU
import InitECandidate.Runtime.HashTableValuesInReadyUpdatesKU
import InitECandidate.Runtime.HashTableValuesInSetExistingLookupKU
/-! Unaligned-key copy of `HashTableValuesInSetUnsafe` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_unsafe_growth_values_in_dichotomyKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 54 * capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    (∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer post ∧
      HashTableValuesIn table targets post ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      state.clock ≤ post.clock + 54 * capacity.toNat + 9 ∧ post.clock ≤ state.clock) ∨
    ((evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock + 54 * capacity.toNat + 9 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock) := by
  obtain ⟨found,ready,_,decl,failed⟩ := invariant.live.arrays.set_lookup_failure_terminal_supported_no_timeoutKU state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
    tableLocal keyLocal valueLocal keyAligned len8 keyFit keyWords keyBytes budget heap pointerBound notSafe loadFactor
  obtain ⟨existing,other,otherDecl,present⟩ := invariant.set_lookup_existing_values_inKU state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
    targets registered member (by omega) tableLocal keyLocal valueLocal keyAligned len8 keyFit keyWords keyBytes
  have equal := declaration_word_result_unique state ready other (ofString "i") (ofString "htab_find_slot")
    [.var .local (ofString "t"),.var .local (ofString "key")] found existing decl otherDecl
  by_cases missing : found = capacity
  · exact Or.inr (failed missing)
  · have different : existing ≠ capacity := by rw [← equal]; exact missing
    obtain ⟨post,run,ready,postRegistered,cost,remaining,code,domain,endian⟩ := present different
    exact Or.inl ⟨post,run,ready,postRegistered,code,domain,endian,by omega,remaining⟩

#print axioms HashTableReady.set_unsafe_growth_values_in_dichotomyKU
end InitECandidate.Runtime

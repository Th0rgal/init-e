import InitECandidate.Runtime.HashTableValuesInSetCallUnsafe
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
import InitECandidate.Runtime.HashTableValuesInSetUnsafeKU
/-! Unaligned-key copy of `HashTableValuesInSetCallUnsafe` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual set call either updates an existing key with a physical frame or
terminates without timeout when the selected growth allocation fails. -/
theorem HashTableReady.set_unsafe_growth_call_values_in_dichotomyKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 54 * capacity.toNat + 10 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) =
      (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer post ∧
      HashTableValuesIn table targets post ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      state.clock ≤ post.clock + 54 * capacity.toNat + 10 ∧ post.clock ≤ state.clock) ∨
    ((evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ none ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 54 * capacity.toNat + 10 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := invariant.after_read state entry keyLength table keys stride capacity used values order orderPos count bits pointer rfl rfl rfl rfl rfl
  have installed : state.code.lookup (ofString "htab_set") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [invariant.live.arrays.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_htab_set) table key value (by decide) (by decide) (by decide) installed
  have outcome := entryReady.set_unsafe_growth_values_in_dichotomyKU entry keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
    targets (registered.after_read rfl rfl rfl) member t k v keyAligned len8 keyFit keyWords keyBytes (by change 54 * capacity.toNat + 9 ≤ state.clock - 1; omega)
    heap pointerBound notSafe loadFactor
  rcases outcome with success | failure
  · obtain ⟨post,run,valid,postRegistered,code,domain,endian,cost,remaining⟩ := success
    have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
      (sourceFunctionBody Guest.guestFn_htab_set) callee .one (.val (.word 0)) post arguments lookup (by omega) run
      (by simp [shapeOfHOLExact,shapeEqHOL])
    refine Or.inl ⟨{post with locals := state.locals},call,
      valid.after_read post _ keyLength table keys stride capacity used values order orderPos count bits pointer rfl rfl rfl rfl rfl,
      postRegistered.after_read rfl rfl rfl,rfl,code,domain,endian,?_,?_⟩
    · change state.clock - 1 ≤ post.clock + 54 * capacity.toNat + 9 at cost
      change state.clock ≤ post.clock + 54 * capacity.toNat + 10
      omega
    · change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega
  · obtain ⟨_,noTimeout,noReturn,_,cost,remaining⟩ := failure
    let evaluated := evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)
    have terminal := evaluate_discard_call_body_terminal state evaluated.2 (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
      (sourceFunctionBody Guest.guestFn_htab_set) callee .one evaluated.1 arguments lookup (by omega) rfl noReturn
    have timeout := evaluate_discard_call_body_no_timeout state evaluated.2 (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
      (sourceFunctionBody Guest.guestFn_htab_set) callee .one evaluated.1 arguments lookup (by omega) rfl noTimeout
    have clock := evaluate_discard_call_body_clock state evaluated.2 (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
      (sourceFunctionBody Guest.guestFn_htab_set) callee .one evaluated.1 arguments lookup (by omega) rfl
    refine Or.inr ⟨terminal,timeout,(fun output => evaluate_discard_call_no_return state _ _ output),evaluate_discard_call_no_continue state _ _,?_,?_⟩
    · rw [clock]
      change state.clock - 1 ≤ evaluated.2.clock + 54 * capacity.toNat + 9 at cost
      omega
    · rw [clock]
      change evaluated.2.clock ≤ state.clock - 1 at remaining
      omega

#print axioms HashTableReady.set_unsafe_growth_call_values_in_dichotomyKU
end InitECandidate.Runtime

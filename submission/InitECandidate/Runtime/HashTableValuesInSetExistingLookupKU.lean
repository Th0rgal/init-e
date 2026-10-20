import InitECandidate.Runtime.HashTableValuesInSetExistingLookup
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
/-! Unaligned-key copy of `HashTableValuesInSetExistingLookup` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_lookup_existing_values_inKU {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (ticks : 54 * capacity.toNat + 2 ≤ state.clock)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ found : BitVec 64, ∃ lookupState : PanSemStateFiniteExact 64 F,
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall (ofString "i") .one (ofString "htab_find_slot")
          [.var .local (ofString "t"),.var .local (ofString "key")] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word found)) lookupState) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "i",state.locals.lookup (ofString "i")))}))) ∧
      (found ≠ capacity → ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 54 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) := by
  have invariant := initialReady.live.arrays
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find_supportedKU state keyLength table keys stride capacity used values order orderPos items key bits supported _ _ arguments keyAligned len8 keyFit sourceWordDomain sourceByteDomain (by omega)
  refine ⟨found,ready,decl (ofString "i"),?_⟩
  intro different
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
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have strict : found.toNat < capacity.toNat := by
    have ne : found.toNat ≠ capacity.toNat := fun equal => different (BitVec.eq_of_toNat_eq equal)
    omega
  obtain ⟨post,run,valid,postRegistered,_,clock,_,postCode,postAddresses,postEndian⟩ :=
    entryReady.set_existing_values_in_frame entered keyLength table pointer keys stride capacity used values order orderPos items found value bits
      t i v strict hashSetMissing targets entryRegistered member
  rw [source_hashSet_existing,decl,run]
  refine ⟨_,rfl,(valid.after_read post _ keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl),
    postRegistered.after_read rfl rfl rfl,?_,?_,postCode.trans code,postAddresses.trans addresses,postEndian.trans endian⟩
  · change state.clock ≤ post.clock + 54 * capacity.toNat + 2
    change post.clock = ready.clock at clock
    omega
  · change post.clock ≤ state.clock
    change post.clock = ready.clock at clock
    omega
#print axioms HashTableReady.set_lookup_existing_values_inKU
end InitECandidate.Runtime

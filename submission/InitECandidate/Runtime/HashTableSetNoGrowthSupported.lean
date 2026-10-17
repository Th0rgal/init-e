import InitECandidate.Runtime.HashTableArraysFindSupported
import InitECandidate.Runtime.HashTableSetExistingLinkedWidth
import InitECandidate.Runtime.HashTableSetMissingSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original set body below its growth threshold, including either
lookup outcome and preserving the invariant with unchanged or successor count. -/
theorem HashTableArraysInvariant.set_no_growth_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (orderEntries : HashOrderEntriesBound order capacity count state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos nextCount bits post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity nextCount post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      HashOrderLinked used order orderPos capacity nextCount post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find_supported state keyLength table keys stride capacity used values order orderPos count key bits supported _ _ arguments keyAligned sourceWordDomain sourceByteDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read ready entered keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredValues := entries.after_read state entered used values capacity memory addresses endian
  have enteredReverse := reverseEntries.after_read state entered used orderPos capacity count memory addresses endian
  have enteredOrder := orderEntries.after_memory state entered order capacity count memory
  have enteredLinked := linked.after_read state entered used order orderPos capacity count memory addresses endian
  have branch : ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos nextCount bits post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity nextCount post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      HashOrderLinked used order orderPos capacity nextCount post ∧
      entered.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ entered.clock ∧
      post.globals = entered.globals ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
      have words : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
        change ∀ offset : Nat, _ → ready.memaddrs _
        rw [addresses]; exact sourceWordDomain
      have bytes : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
        change ∀ offset : Nat, _ → ready.memaddrs _
        rw [addresses]; exact sourceByteDomain
      obtain ⟨post,run,postValid,ordered,valuesOk,reverseOk,postLinked,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        validEntry.set_missing_no_growth_supported entered keyLength table keys stride capacity used values order orderPos count key value bits supported t k v keyAligned words bytes loadFactor
          (by change capacity.toNat + keyLength.toNat + 3 ≤ ready.clock; omega) enteredOrder enteredValues enteredReverse enteredLinked keysBeforeValues
      exact ⟨count + 1,post,Or.inr rfl,selected.trans run,postValid,valuesOk,reverseOk,ordered,postLinked,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,postValid,valuesOk,reverseOk,ordered,clock,tailGlobals,tailCode,tailAddresses,tailEndian,postLinked⟩ :=
        validEntry.set_existing_tail_linked_width entered keyLength table keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing enteredValues enteredReverse enteredOrder enteredLinked
      exact ⟨count,post,Or.inl rfl,run,postValid,valuesOk,reverseOk,ordered,postLinked,by omega,by omega,tailGlobals,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨nextCount,post,counts,tail,postValid,valuesOk,reverseOk,ordered,postLinked,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨nextCount,_,counts,rfl,postValid.after_read post _ keyLength table keys stride capacity used values order orderPos nextCount bits rfl rfl rfl rfl,
    valuesOk.after_read post _ used values capacity rfl rfl rfl,
    reverseOk.after_read post _ used orderPos capacity nextCount rfl rfl rfl,
    ordered.after_memory post _ order capacity nextCount rfl,
    postLinked.after_read post _ used order orderPos capacity nextCount rfl rfl rfl,?_,?_,
    tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5
    change ready.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ ready.clock at tailRemaining
    omega

#print axioms HashTableArraysInvariant.set_no_growth_supported
end InitECandidate.Runtime

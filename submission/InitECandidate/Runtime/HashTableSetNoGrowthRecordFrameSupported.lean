import InitECandidate.Runtime.HashTableSetExistingRecordFrame
import InitECandidate.Runtime.HashTableSetMissingRecordFrameSupported
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete no-growth set body preserves both target and earlier table. -/
theorem HashTableReady.set_no_growth_supported_with_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock)
    (journal : BitVec 64) (journalCount : Nat)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (beforeKeys : journal.toNat + journalCount * 32 ≤ keys.toNat)
    (beforeValues : journal.toNat + journalCount * 32 ≤ values.toNat)
    (separateHeader : journal.toNat + journalCount * 32 ≤ table.toNat ∨ table.toNat + 72 ≤ journal.toNat) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,lookupState,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    ready.live.arrays.find_supported state keyLength table keys stride capacity used values order orderPos count key bits supported _ _ arguments keyAligned sourceWordDomain sourceByteDomain (by omega)
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
  have branch : ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          entered.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
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
      obtain ⟨post,run,valid,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_missing_supported_with_record_frame entered keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
          t k v keyAligned words bytes loadFactor (by change capacity.toNat + keyLength.toNat + 3 ≤ lookupState.clock; omega)
          journal journalCount journalBound beforeKeys beforeValues separateHeader
      exact ⟨count + 1,post,Or.inr rfl,selected.trans run,valid,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,valid,otherValid,clock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_existing_with_record_frame entered keyLength table pointer keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing
          journal journalCount journalBound (Or.inr beforeValues)
      exact ⟨count,post,Or.inl rfl,run,valid,otherValid,by omega,by omega,tailGlobals,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨nextCount,post,counts,tail,postReady,postOther,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨nextCount,_,counts,rfl,
    postReady.after_read post _ keyLength table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl,
    (by
      intro index inside offset member
      exact (postOther index inside offset member).trans (congrFun memory _)),
    ?_,?_,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5
    change lookupState.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ lookupState.clock at tailRemaining
    omega

#print axioms HashTableReady.set_no_growth_supported_with_record_frame
end InitECandidate.Runtime

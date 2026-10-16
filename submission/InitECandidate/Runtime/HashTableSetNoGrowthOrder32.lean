import InitECandidate.Runtime.HashTableSetExistingOrder32
import InitECandidate.Runtime.HashTableSetMissingOrder32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original set body below its growth threshold, including either
lookup outcome and preserving the invariant with unchanged or successor count. -/
theorem HashTableArraysInvariant32.set_no_growth_order {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + 37 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos nextCount bits post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + 37 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find state table keys stride capacity used values order orderPos count key bits _ _ arguments keyAligned keyDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read ready entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have entryEntries := entries.after_memory state entered order capacity count memory
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have branch : ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos nextCount bits post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      entered.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ entered.clock ∧
      post.globals = entered.globals ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
      have words : ∀ offset : Nat, offset < 32 → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
        change ∀ offset : Nat, _ → ready.memaddrs _
        rw [addresses]; exact sourceWordDomain
      have bytes : ∀ offset : Nat, offset < 32 → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
        change ∀ offset : Nat, _ → ready.memaddrs _
        rw [addresses]; exact sourceByteDomain
      obtain ⟨post,run,postValid,postEntries,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        validEntry.set_missing_no_growth_order entered table keys stride capacity used values order orderPos count key value bits t k v keyAligned words bytes loadFactor
          (by change capacity.toNat + 35 ≤ ready.clock; omega) entryEntries
      exact ⟨count + 1,post,Or.inr rfl,selected.trans run,postValid,postEntries,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,postValid,postEntries,clock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        validEntry.set_existing_tail_order entered table keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing entryEntries
      exact ⟨count,post,Or.inl rfl,run,postValid,postEntries,by omega,by omega,tailGlobals,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨nextCount,post,counts,tail,postValid,postEntries,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨nextCount,_,counts,rfl,postValid.after_read post _ table keys stride capacity used values order orderPos nextCount bits rfl rfl rfl rfl,postEntries.after_memory post _ order capacity nextCount rfl,?_,?_,
    tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + 37
    change ready.clock ≤ post.clock + capacity.toNat + 35 at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ ready.clock at tailRemaining
    omega

#print axioms HashTableArraysInvariant32.set_no_growth_order
end InitECandidate.Runtime

import InitECandidate.Runtime.HashTableSetExistingAllEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_lookup_all_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits ready ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall (ofString "i") .one (ofString "htab_find_slot")
          [.var .local (ofString "t"),.var .local (ofString "key")] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "i",state.locals.lookup (ofString "i")))}))) ∧
      (found ≠ capacity → ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
          (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
        HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post ∧
        HashOrderEntriesBound order capacity count post ∧
        HashValueEntriesWord used values capacity post ∧
        HashReverseEntriesBound used orderPos capacity count post ∧
        state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
        post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find state table keys stride capacity used values order orderPos count key bits _ _ arguments keyAligned keyDomain budget
  refine ⟨found,ready,inside,valid,decl (ofString "i"),?_⟩
  intro different
  have strictly : found.toNat < capacity.toNat := by
    have ne : found.toNat ≠ capacity.toNat := fun same => different (BitVec.eq_of_toNat_eq same)
    omega
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read ready entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have entryEntries := entries.after_memory state entered order capacity count memory
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,postValid,postValues,postReverse,postEntries,clock,postGlobals,postCode,postAddresses,postEndian⟩ :=
    validEntry.set_existing_tail_all_entries entered table keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing
      (valueEntries.after_read state entered used values capacity memory addresses endian)
      (reverseEntries.after_read state entered used orderPos capacity count memory addresses endian) entryEntries
  rw [source_hashSet_existing,decl,tail]
  refine ⟨_,rfl,postValid.after_read post _ table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl,postEntries.after_memory post _ order capacity count rfl,
    postValues.after_read post _ used values capacity rfl rfl rfl,
    postReverse.after_read post _ used orderPos capacity count rfl rfl rfl,?_,?_,
    postGlobals.trans globals,postCode.trans code,postAddresses.trans addresses,postEndian.trans endian⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2
    change post.clock = ready.clock at clock
    omega
  · change post.clock ≤ state.clock
    change post.clock = ready.clock at clock
    omega

#print axioms HashTableArraysInvariant32.set_lookup_all_entries
end InitECandidate.Runtime

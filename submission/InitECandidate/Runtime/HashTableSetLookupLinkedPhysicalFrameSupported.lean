import InitECandidate.Runtime.HashTablePhysicalFrame
import InitECandidate.Runtime.JournalUndoRecordsRead
import InitECandidate.Runtime.HashTableSetExistingLinkedWidth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.set_lookup_supported_linked_physical_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (linked : HashOrderLinked used order orderPos capacity count state)
 :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits ready ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall (ofString "i") .one (ofString "htab_find_slot")
          [.var .local (ofString "t"),.var .local (ofString "key")] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "i",state.locals.lookup (ofString "i")))}))) ∧
      (found ≠ capacity → ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
          (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
        HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits post ∧
        HashOrderEntriesBound order capacity count post ∧
        HashValueEntriesWord used values capacity post ∧
        HashReverseEntriesBound used orderPos capacity count post ∧
        HashOrderLinked used order orderPos capacity count post ∧
        state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
        post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
          post.memory address = state.memory address)) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find_supported state keyLength table keys stride capacity used values order orderPos count key bits supported _ _ arguments keyAligned keyWords keyBytes budget
  refine ⟨found,ready,inside,valid,decl (ofString "i"),?_⟩
  intro different
  have strictly : found.toNat < capacity.toNat := by
    have ne : found.toNat ≠ capacity.toNat := fun same => different (BitVec.eq_of_toNat_eq same)
    omega
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read ready entered keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have entryEntries := entries.after_memory state entered order capacity count memory
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,postValid,postValues,postReverse,postEntries,clock,postGlobals,postCode,postAddresses,postEndian,postLinked⟩ :=
    validEntry.set_existing_tail_linked_width entered keyLength table keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing
      (valueEntries.after_read state entered used values capacity memory addresses endian)
      (reverseEntries.after_read state entered used orderPos capacity count memory addresses endian) entryEntries
      (linked.after_read state entered used order orderPos capacity count memory addresses endian)
  have facts := validEntry.insertion_memory entered keyLength table keys stride capacity used values order orderPos count bits
  have checked := evaluate_hashSet_existing_tail entered table found capacity values value hashSetMissing different t i v
    (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
    (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos count bits 40 (by decide)) validEntry.cell40 (facts.valueDomain found strictly)
  have same : post = emptyLocalsHOLFinite (sourceWriteWord entered (values + found * 8) value) := congrArg Prod.snd (tail.symm.trans checked)
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have address := (hashFind_slot_address values found 8 capacity strictly
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.valuesAligned (by decide)).1
  change (values + found * 8).toNat = values.toNat + found.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right strictly (by decide : 0 < 8)
  have postFrame : ∀ watched : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos watched →
      post.memory watched = state.memory watched := by
    intro watched outside
    have different : watched ≠ values + found * 8 := by
      intro equal
      apply outside
      rw [equal]
      unfold tablePhysicalRegion
      omega
    rw [same]
    change (sourceWriteWord entered (values + found * 8) value).memory watched = _
    have retained : (sourceWriteWord entered (values + found * 8) value).memory watched = entered.memory watched := by
      simp only [sourceWriteWord]
      simp
      intro equal
      exact False.elim (different equal)
    exact retained.trans (congrFun memory _)
  rw [source_hashSet_existing,decl,tail]
  refine ⟨_,rfl,postValid.after_read post _ keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl,postEntries.after_memory post _ order capacity count rfl,
    postValues.after_read post _ used values capacity rfl rfl rfl,
    postReverse.after_read post _ used orderPos capacity count rfl rfl rfl,
    postLinked.after_read post _ used order orderPos capacity count rfl rfl rfl,?_,?_,
    postGlobals.trans globals,postCode.trans code,postAddresses.trans addresses,postEndian.trans endian,postFrame⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2
    change post.clock = ready.clock at clock
    omega
  · change post.clock ≤ state.clock
    change post.clock = ready.clock at clock
    omega

#print axioms HashTableArraysInvariant.set_lookup_supported_linked_physical_frame
end InitECandidate.Runtime

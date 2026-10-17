import InitECandidate.Runtime.HashDeleteLookupSource
import InitECandidate.Runtime.HashDeleteCapacityScopeAllSupported
import InitECandidate.Runtime.HashTableArraysFindOccupiedSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original deletion body, including lookup, both guard outcomes,
cluster movement and final bookkeeping. -/
theorem evaluate_source_hashDelete_supported_all {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat * 57 + 2 ≤ state.clock) :
    ∃ result : BitVec 64, ∃ post,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_del) =
        (some (.returned (.val (.word result))),post) ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 2 ∧ post.clock ≤ state.clock ∧
      ((result = 0 ∧ HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits post ∧ HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity items post ∧ HashReverseEntriesBound used orderPos capacity items post ∧ HashOrderLinked used order orderPos capacity items post) ∨
       (result = 1 ∧ HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (items - 1) bits post ∧ HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity (items - 1) post ∧ HashReverseEntriesBound used orderPos capacity (items - 1) post ∧ HashOrderLinked used order orderPos capacity (items - 1) post)) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,occupied,findCost,findRemaining,memory,globals,code,domain,endian,locals,readyInvariant,decl⟩ :=
    invariant.find_supported_occupied state keyLength table keys stride capacity used values order orderPos items key bits supported
      _ _ arguments keyAligned keyWords keyBytes (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have iLocal : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have notTable : ofString "i" ≠ ofString "t" := by decide
  have tLocal : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notTable,locals] using tableLocal
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits memory code domain endian
  have enteredLinked := linked.after_read state entered used order orderPos capacity items memory domain endian
  rw [source_hashDelete_lookup_prefix,decl]
  change ∃ result post, (let output := evaluateHOLFiniteState entered (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)); _) = _ ∧ _
  classical
  by_cases missing : found = capacity
  · have iCapacity : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by simpa [missing] using iLocal
    obtain ⟨post,run,ticks,arrays,words,orderEntries,reverseEntries,postLinked⟩ := enteredInvariant.delete_all_capacity_scope_missing_supported entered
      keyLength table keys stride capacity used values order orderPos items bits (entries.after_read state entered used values capacity memory domain endian)
      (ordered.after_memory state entered order capacity items memory)
      (reverse.after_read state entered used orderPos capacity items memory domain endian) enteredLinked tLocal iCapacity
    rw [run]
    refine ⟨0,_,rfl,?_,?_,Or.inl ⟨rfl,?_⟩⟩
    · change state.clock ≤ post.clock + capacity.toNat * 57 + 2
      change post.clock = ready.clock at ticks
      omega
    · change post.clock ≤ state.clock
      change post.clock = ready.clock at ticks
      omega
    · exact ⟨arrays.after_read post _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
        words.after_read post _ used values capacity rfl rfl rfl,
        orderEntries.after_memory post _ order capacity items rfl,
        reverseEntries.after_read post _ used orderPos capacity items rfl rfl rfl,
        postLinked.after_read post _ used order orderPos capacity items rfl rfl rfl⟩
  · have foundInside : found.toNat < capacity.toNat := by
      have differentNat : found.toNat ≠ capacity.toNat := fun equal => missing (BitVec.eq_of_toNat_eq equal)
      omega
    obtain ⟨post,run,cost,remaining,arrays,words,orderEntries,reverseEntries,postLinked⟩ := enteredInvariant.delete_all_capacity_scope_from_hole_supported entered
      keyLength table keys stride capacity used values order orderPos items found bits
      (entries.after_read state entered used values capacity memory domain endian)
      (reverse.after_read state entered used orderPos capacity items memory domain endian)
      (ordered.after_memory state entered order capacity items memory) keyValueOrder foundInside (occupied missing)
      iLocal enteredLinked tLocal supported (by change capacity.toNat * 55 ≤ ready.clock; omega)
    rw [run]
    refine ⟨1,_,rfl,?_,?_,Or.inr ⟨rfl,?_⟩⟩
    · change state.clock ≤ post.clock + capacity.toNat * 57 + 2
      change ready.clock ≤ post.clock + capacity.toNat * 55 at cost
      omega
    · change post.clock ≤ state.clock
      change post.clock ≤ ready.clock at remaining
      omega
    · exact ⟨arrays.after_read post _ keyLength table keys stride capacity used values order orderPos (items - 1) bits rfl rfl rfl rfl,
        words.after_read post _ used values capacity rfl rfl rfl,
        orderEntries.after_memory post _ order capacity (items - 1) rfl,
        reverseEntries.after_read post _ used orderPos capacity (items - 1) rfl rfl rfl,
        postLinked.after_read post _ used order orderPos capacity (items - 1) rfl rfl rfl⟩

#print axioms evaluate_source_hashDelete_supported_all
end InitECandidate.Runtime

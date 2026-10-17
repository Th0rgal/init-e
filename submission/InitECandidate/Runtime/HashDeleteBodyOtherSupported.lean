import InitECandidate.Runtime.HashDeleteLookupSource
import InitECandidate.Runtime.HashDeleteCapacityScopeOtherSupported
import InitECandidate.Runtime.HashDeleteCapacityMissingOtherWidth
import InitECandidate.Runtime.HashTableArraysFindOccupiedSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original deletion body, including lookup, both guard outcomes,
cluster movement and final bookkeeping. -/
theorem evaluate_source_hashDelete_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 57 + 2 ≤ state.clock) :
    ∃ result : BitVec 64, ∃ post,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_del) =
        (some (.returned (.val (.word result))),post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 2 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  have enteredOther := otherReady.after_read state entered otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code domain endian
  rw [source_hashDelete_lookup_prefix,decl]
  change ∃ result post, (let output := evaluateHOLFiniteState entered (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)); _) = _ ∧ _
  classical
  by_cases missing : found = capacity
  · have iCapacity : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by simpa [missing] using iLocal
    obtain ⟨post,run,preserved,ticks,postGlobals,postCode,postDomain,postEndian⟩ := enteredInvariant.delete_capacity_scope_with_other_missing_width entered
      keyLength table keys stride capacity used values order orderPos items bits enteredLinked tLocal iCapacity
      otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther
    rw [run]
    refine ⟨0,_,rfl,preserved.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,?_,?_,postGlobals.trans globals,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
    · change state.clock ≤ post.clock + capacity.toNat * 57 + 2
      change post.clock = ready.clock at ticks
      omega
    · change post.clock ≤ state.clock
      change post.clock = ready.clock at ticks
      omega
  · have foundInside : found.toNat < capacity.toNat := by
      have differentNat : found.toNat ≠ capacity.toNat := fun equal => missing (BitVec.eq_of_toNat_eq equal)
      omega
    obtain ⟨post,run,preserved,cost,remaining,postGlobals,postCode,postDomain,postEndian⟩ := enteredInvariant.delete_capacity_scope_with_other_from_hole_supported entered
      keyLength table keys stride capacity used values order orderPos items found bits
      (entries.after_read state entered used values capacity memory domain endian)
      (reverse.after_read state entered used orderPos capacity items memory domain endian)
      (ordered.after_memory state entered order capacity items memory) keyValueOrder foundInside (occupied missing)
      iLocal enteredLinked tLocal
      otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther separated supported (by change capacity.toNat * 55 ≤ ready.clock; omega)
    rw [run]
    refine ⟨1,_,rfl,preserved.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,?_,?_,postGlobals.trans globals,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
    · change state.clock ≤ post.clock + capacity.toNat * 57 + 2
      change ready.clock ≤ post.clock + capacity.toNat * 55 at cost
      omega
    · change post.clock ≤ state.clock
      change post.clock ≤ ready.clock at remaining
      omega

#print axioms evaluate_source_hashDelete_supported_with_other
end InitECandidate.Runtime

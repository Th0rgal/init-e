import InitECandidate.Runtime.HashTableSetMissingGrowthFrontier32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_lookup_growth_frontier {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall (ofString "i") .one (ofString "htab_find_slot")
          [.var .local (ofString "t"),.var .local (ofString "key")] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "i",state.locals.lookup (ofString "i")))}))) ∧
      (found = capacity → ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) (items + 1) post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      HashTableHeapFrontier32 (htabGrowOrderPos pointer capacity stride) (capacity * 2)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) := by
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
    invariant.find state table keys stride capacity used values order orderPos items key bits _ _ arguments keyAligned keyDomain (by omega)
  refine ⟨found,ready,inside,decl (ofString "i"),?_⟩
  intro same
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry := valid.after_read ready entered table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have entryEntries := entries.after_memory state entered order capacity items memory
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
  have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
    (validEntry.header_domain entered table keys stride capacity used values order orderPos items bits 16 (by decide)) validEntry.cell16
  have heapEntry : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact heap
  have domainEntry : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → entered.memaddrs address := by
    change ∀ address : BitVec 64, _ → _ → ready.memaddrs address
    rw [addresses]; exact domain
  have words : ∀ offset : Nat, offset < 32 → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceWordDomain
  have bytes : ∀ offset : Nat, offset < 32 → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    change ∀ offset : Nat, _ → ready.memaddrs _
    rw [addresses]; exact sourceByteDomain
  obtain ⟨post,tail,postValid,postEntries,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian,tailFrontier⟩ :=
    validEntry.set_missing_growth_frontier entered table pointer keys stride capacity used values order orderPos items key value bits
      entryEntries allocated strideBound pointerAligned pointerBound capacityBound safePlan
      (by change 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) ≤ ready.clock; omega)
      heapEntry domainEntry t k v loadFactor capacityLarge keyAligned words bytes
  have bodyTail := selected.trans tail
  rw [source_hashSet_existing,decl,bodyTail]
  refine ⟨_,rfl,postValid.after_read post _ table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      (items + 1) (bits + 1) rfl rfl rfl rfl,
    postEntries.after_memory post _ _ _ _ rfl,?_,?_,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian,
    tailFrontier.after_globals post _ _ _ _ rfl⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36)
    change ready.clock ≤ post.clock + 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ ready.clock at tailRemaining
    omega

#print axioms HashTableArraysInvariant32.set_lookup_growth_frontier
end InitECandidate.Runtime

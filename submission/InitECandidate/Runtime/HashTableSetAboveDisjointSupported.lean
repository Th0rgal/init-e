import InitECandidate.Runtime.HashTableSetMissingGrowthOtherSupported
import InitECandidate.Runtime.HashTableSetExistingOtherWidth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete above-threshold set body preserves target and protected table. -/
theorem HashTableReady.set_above_supported_with_disjoint_values {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (above : capacity.toNat < (items.toNat + 1) * 2) (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (valueSeparate : values.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨ (HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
  obtain ⟨found,lookupState,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    ready.live.arrays.find_supported state keyLength table keys stride capacity used values order orderPos items key bits supported _ _ arguments keyAligned sourceWordDomain sourceByteDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) lookupState
  have validEntry : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits entered :=
    valid.after_read lookupState entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans t
  have k := (other (ofString "key") (by decide)).trans k
  have v := (other (ofString "value") (by decide)).trans v
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := ready.after_read state entered keyLength table keys stride capacity used values order orderPos items bits pointer memory globals code addresses endian
  have enteredOther := otherReady.after_read state entered otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code addresses endian
  have branch : ∃ post, evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨ (HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      entered.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ entered.clock ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) validEntry.cell16
      obtain ⟨post,run,valid,otherValid,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_missing_growth_supported_with_other entered keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
          t k v strideBound safePlan (by change 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ lookupState.clock; omega)
          (by change ∀ address, _ → _ → lookupState.memaddrs address; rw [addresses]; exact domain) above capacityLarge keyAligned
          (by change ∀ offset, _ → lookupState.memaddrs _; rw [addresses]; exact sourceWordDomain)
          (by change ∀ offset, _ → lookupState.memaddrs _; rw [addresses]; exact sourceByteDomain)
          otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther separate
      exact ⟨post,selected.trans run,Or.inr ⟨valid,otherValid⟩,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,valid,otherValid,clock,_,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_existing_with_other_width entered keyLength table pointer keys stride capacity used values order orderPos items found value bits t i v strictly hashSetMissing
          otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther valueSeparate
      exact ⟨post,run,Or.inl ⟨valid,otherValid⟩,by omega,by omega,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨post,tail,cases,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨_,rfl,?_,?_,?_,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · rcases cases with unchanged | grown
    · exact Or.inl ⟨unchanged.1.after_read post _ keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
        unchanged.2.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩
    · exact Or.inr ⟨grown.1.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
        grown.2.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
    change lookupState.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ lookupState.clock at tailRemaining
    omega

#print axioms HashTableReady.set_above_supported_with_disjoint_values
end InitECandidate.Runtime

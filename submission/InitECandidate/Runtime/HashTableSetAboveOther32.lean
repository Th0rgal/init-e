import InitECandidate.Runtime.HashTableSetMissingGrowthOther32
import InitECandidate.Runtime.HashTableSetExistingOther32
import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete above-threshold set body preserves target and protected table. -/
theorem HashTableReady32.set_above_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (above : capacity.toNat < (items.toNat + 1) * 2) (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨ (HashTableReady32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨found,lookupState,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    ready.live.arrays.find state table keys stride capacity used values order orderPos items key bits _ _ arguments keyAligned keyDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) lookupState
  have validEntry : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits entered :=
    valid.after_read lookupState entered table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans t
  have k := (other (ofString "key") (by decide)).trans k
  have v := (other (ofString "value") (by decide)).trans v
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := ready.after_read state entered table keys stride capacity used values order orderPos items bits pointer memory globals code addresses endian
  have enteredOther := otherReady.after_read state entered otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code addresses endian
  have branch : ∃ post, evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨ (HashTableReady32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      entered.clock ≤ post.clock + 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ entered.clock ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered table keys stride capacity used values order orderPos items bits 16 (by decide)) validEntry.cell16
      obtain ⟨post,run,valid,otherValid,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_missing_growth_with_other entered table pointer keys stride capacity used values order orderPos items key value bits
          t k v strideBound safePlan (by change 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) ≤ lookupState.clock; omega)
          (by change ∀ address, _ → _ → lookupState.memaddrs address; rw [addresses]; exact domain) above capacityLarge keyAligned
          (by change ∀ offset, _ → lookupState.memaddrs _; rw [addresses]; exact sourceWordDomain)
          (by change ∀ offset, _ → lookupState.memaddrs _; rw [addresses]; exact sourceByteDomain)
          otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther separate
      exact ⟨post,selected.trans run,Or.inr ⟨valid,otherValid⟩,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,valid,otherValid,clock,_,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_existing_with_other entered table pointer keys stride capacity used values order orderPos items found value bits t i v strictly hashSetMissing
          otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther (Or.inr beforeValues)
      exact ⟨post,run,Or.inl ⟨valid,otherValid⟩,by omega,by omega,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨post,tail,cases,tailCost,tailRemaining,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨_,rfl,?_,?_,?_,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · rcases cases with unchanged | grown
    · exact Or.inl ⟨unchanged.1.after_read post _ table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
        unchanged.2.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩
    · exact Or.inr ⟨grown.1.after_read post _ table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
        grown.2.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36)
    change lookupState.clock ≤ post.clock + 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ lookupState.clock at tailRemaining
    omega

#print axioms HashTableReady32.set_above_with_other
end InitECandidate.Runtime

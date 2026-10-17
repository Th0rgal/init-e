import InitECandidate.Runtime.HashTableSetExistingOther32
import InitECandidate.Runtime.HashTableSetMissingOther32
import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete no-growth set body preserves both target and earlier table. -/
theorem HashTableReady32.set_no_growth_with_earlier_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos count bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + 37 ≤ state.clock)
    (otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (separateHeader : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
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
  obtain ⟨found,lookupState,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    ready.live.arrays.find state table keys stride capacity used values order orderPos count key bits _ _ arguments keyAligned keyDomain (by omega)
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) lookupState
  have validEntry : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits entered :=
    valid.after_read lookupState entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ne
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,locals]
  have t := (other (ofString "t") (by decide)).trans tableLocal
  have k := (other (ofString "key") (by decide)).trans keyLocal
  have v := (other (ofString "value") (by decide)).trans valueLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := ready.after_read state entered table keys stride capacity used values order orderPos count bits pointer memory globals code addresses endian
  have enteredOther := otherReady.after_read state entered otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer memory globals code addresses endian
  have branch : ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState entered (hashSetExistingTail hashSetMissing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
      entered.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ entered.clock ∧
      post.globals = entered.globals ∧ post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases same : found = capacity
    · have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by rw [i,same]
      have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
        (validEntry.header_domain entered table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
      have words : ∀ offset : Nat, offset < 32 → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
        change ∀ offset : Nat, _ → lookupState.memaddrs _
        rw [addresses]; exact sourceWordDomain
      have bytes : ∀ offset : Nat, offset < 32 → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
        change ∀ offset : Nat, _ → lookupState.memaddrs _
        rw [addresses]; exact sourceByteDomain
      obtain ⟨post,run,valid,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_missing_with_earlier_table entered table pointer keys stride capacity used values order orderPos count key value bits
          t k v keyAligned words bytes loadFactor (by change capacity.toNat + 35 ≤ lookupState.clock; omega)
          otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
          enteredOther beforeKeys beforeValues separateHeader
      exact ⟨count + 1,post,Or.inr rfl,selected.trans run,valid,otherValid,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩
    · have strictly : found.toNat < capacity.toNat := by
        have ne : found.toNat ≠ capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      obtain ⟨post,run,valid,otherValid,clock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
        enteredReady.set_existing_with_other entered table pointer keys stride capacity used values order orderPos count found value bits t i v strictly hashSetMissing
          otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther (Or.inr beforeValues)
      exact ⟨count,post,Or.inl rfl,run,valid,otherValid,by omega,by omega,tailGlobals,tailCode,tailAddresses,tailEndian⟩
  obtain ⟨nextCount,post,counts,tail,postReady,postOther,tailCost,tailRemaining,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := branch
  rw [source_hashSet_existing,decl,tail]
  refine ⟨nextCount,_,counts,rfl,
    postReady.after_read post _ table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl,
    postOther.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer rfl rfl rfl rfl rfl,
    ?_,?_,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + 37
    change lookupState.clock ≤ post.clock + capacity.toNat + 35 at tailCost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ lookupState.clock at tailRemaining
    omega

#print axioms HashTableReady32.set_no_growth_with_earlier_table
end InitECandidate.Runtime

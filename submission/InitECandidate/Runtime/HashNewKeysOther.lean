import InitECandidate.Runtime.HashNewKeysAllocation
import InitECandidate.Runtime.HashNewValuesOther
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabNew_keys_allocation_other_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 6 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd table 72))))
    (safe : AllocationPlanSafe (allocationEnd table 72)
      [capacity * allocationEnd 0 keyLength,capacity * 8,capacity,capacity * 8,capacity * 8])
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))))
    (domain32 : state.memaddrs (table + 32)) (domain40 : state.memaddrs (table + 40)) (domain48 : state.memaddrs (table + 48))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (oldKeyLength otherTable keys stride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (otherReady : HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits (allocationEnd table 72) state)
    (outside : (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (htabNewUsed table keyLength capacity).toNat)
    (outside48 : (table + 48).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 48).toNat)
    (outside56 : (table + 56).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 56).toNat)
    (outside64 : (table + 64).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 64).toNat)
    (outside40 : (table + 40).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 40).toNat)
    (outside32 : (table + 32).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 32).toNat) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterHeader = (some (.returned (.val (.word table))),post) ∧
      HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
        (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) post ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 6 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * allocationEnd 0 keyLength))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,readyOther,clock,locals,_,_,heapNext,postCode,addresses,endian⟩ :=
    otherReady.allocation_pointer_store state (ofString "keys") (ofString "t") _
      (allocationEnd table 72) (capacity * allocationEnd 0 keyLength) table 32 htabNewValuesAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain32
      oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits outside32
  have nt : ofString "keys" ≠ ofString "t" := by decide
  have nc : ofString "keys" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,preserved,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_values_allocation_other_width ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe keyBound tableAligned budget t c
      (by rw [addresses]; exact domain40) (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
      oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits readyOther outside outside48 outside56 outside64 outside40
  rw [source_htabNew_keys_allocation,run]
  rw [tail]
  exact ⟨_,rfl,preserved.after_read post _ oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
    (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) rfl rfl rfl rfl rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 6; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩

#print axioms evaluate_htabNew_keys_allocation_other_width
end InitECandidate.Runtime

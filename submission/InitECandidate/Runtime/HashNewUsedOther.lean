import InitECandidate.Runtime.HashNewUsedAllocation
import InitECandidate.Runtime.HashNewZeroTailOther
import InitECandidate.Runtime.HashTableReadyAllocDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabNew_used_allocation_other_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 4 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (htabNewUsed table keyLength capacity))))
    (safe : AllocationPlanSafe (htabNewUsed table keyLength capacity) [capacity,capacity * 8,capacity * 8])
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (oldKeyLength otherTable keys stride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (otherReady : HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits (htabNewUsed table keyLength capacity) state)
    (outside : (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (htabNewUsed table keyLength capacity).toNat)
    (outside48 : (table + 48).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 48).toNat)
    (outside56 : (table + 56).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 56).toNat)
    (outside64 : (table + 64).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 64).toNat) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedAllocation = (some (.returned (.val (.word table))),post) ∧
      HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
        (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) post ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 4 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "cap")] =
        some [.val (.word capacity)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal]
  obtain ⟨allocated,_,allocatedReady,clock,memory,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    otherReady.alloc_declaration state oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits (htabNewUsed table keyLength capacity) capacity _ arguments (by omega) guard
  let entered := setVarHOLFinite (ofString "used") (.val (.word (htabNewUsed table keyLength capacity))) allocated
  have nt : ofString "used" ≠ ofString "t" := by decide
  have nc : ofString "used" ≠ ofString "cap" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,locals] using tableLocal
  have c : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have u : entered.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have updated : entered.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd (htabNewUsed table keyLength capacity) capacity))) := by
    change allocated.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := allocatedReady.after_read allocated entered oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits (allocationEnd (htabNewUsed table keyLength capacity) capacity) rfl rfl rfl rfl rfl
  obtain ⟨post,tail,preserved,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_zero_tail_other_width entered (allocationEnd (htabNewUsed table keyLength capacity) capacity)
      table keyLength capacity (postCode.trans code) (by change capacity.toNat + 3 ≤ allocated.clock; omega)
      updated restSafe keyBound tableAligned budget t u c
      (by change allocated.memaddrs _; rw [addresses]; exact domain48)
      (by change allocated.memaddrs _; rw [addresses]; exact domain56)
      (by change allocated.memaddrs _; rw [addresses]; exact domain64)
      (by simpa [entered,setVarHOLFinite,addresses] using wordDomain)
      (by simpa [entered,setVarHOLFinite,addresses] using byteDomain)
      oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits enteredReady outside outside48 outside56 outside64
  have enteredClock : entered.clock = state.clock - 1 := clock
  unfold htabNewUsedAllocation
  rw [decl (ofString "used") htabNewUsedBody]
  change (∃ result, (let output := evaluateHOLFiniteState entered htabNewUsedBody; _) = _ ∧ _)
  rw [tail]
  exact ⟨_,rfl,preserved.after_read post _ oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
    (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) rfl rfl rfl rfl rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 4; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩

#print axioms evaluate_htabNew_used_allocation_other_width
end InitECandidate.Runtime

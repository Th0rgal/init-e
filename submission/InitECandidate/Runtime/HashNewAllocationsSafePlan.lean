import InitECandidate.Runtime.HashNewZeroTailSafePlan
import InitECandidate.Runtime.HashNewKeysAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual allocation suffix preserves the empty-table invariant under a
safe constructor plan, without a conservative reserve. -/
theorem evaluate_htabNew_used_allocation_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 4 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (htabNewUsed table keyLength capacity))))
    (safe : AllocationPlanSafe (htabNewUsed table keyLength capacity) [capacity,capacity * 8,capacity * 8])
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedAllocation = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 4 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "cap")] =
        some [.val (.word capacity)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal]
  obtain ⟨allocated,_,clock,_,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state _ (htabNewUsed table keyLength capacity) capacity arguments code
      (by omega) heap guard finish
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
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_zero_tail_of_safe_plan entered (allocationEnd (htabNewUsed table keyLength capacity) capacity)
      table keyLength capacity (postCode.trans code) (by change capacity.toNat + 3 ≤ allocated.clock; omega)
      updated restSafe pointerBound tableAligned fullSafe t u c
      (by change allocated.memaddrs _; rw [addresses]; exact domain48)
      (by change allocated.memaddrs _; rw [addresses]; exact domain56)
      (by change allocated.memaddrs _; rw [addresses]; exact domain64)
      (by simpa [entered,setVarHOLFinite,addresses] using wordDomain)
      (by simpa [entered,setVarHOLFinite,addresses] using byteDomain)
  have enteredClock : entered.clock = state.clock - 1 := clock
  unfold htabNewUsedAllocation
  rw [decl]
  change (∃ result, (let output := evaluateHOLFiniteState entered htabNewUsedBody; _) = _ ∧ _)
  rw [tail]
  exact ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 4; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩


/-- Actual allocation suffix preserves the empty-table invariant under a
safe constructor plan, without a conservative reserve. -/
theorem evaluate_htabNew_values_allocation_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 5 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (htabNewValues table keyLength capacity))))
    (safe : AllocationPlanSafe (htabNewValues table keyLength capacity)
      [capacity * 8,capacity,capacity * 8,capacity * 8])
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain40 : state.memaddrs (table + 40)) (domain48 : state.memaddrs (table + 48))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewValuesAllocation = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,_,_,heapNext,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "vals") (ofString "t") _
      (htabNewValues table keyLength capacity) (capacity * 8) table 40 htabNewUsedAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain40
  have nt : ofString "vals" ≠ ofString "t" := by decide
  have nc : ofString "vals" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_used_allocation_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_values_allocation,run]
  rw [tail]
  exact ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 5; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩


/-- Actual allocation suffix preserves the empty-table invariant under a
safe constructor plan, without a conservative reserve. -/
theorem evaluate_htabNew_keys_allocation_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 6 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd table 72))))
    (safe : AllocationPlanSafe (allocationEnd table 72)
      [capacity * allocationEnd 0 keyLength,capacity * 8,capacity,capacity * 8,capacity * 8])
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))))
    (domain32 : state.memaddrs (table + 32)) (domain40 : state.memaddrs (table + 40)) (domain48 : state.memaddrs (table + 48))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterHeader = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 6 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * allocationEnd 0 keyLength))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,_,_,heapNext,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "keys") (ofString "t") _
      (allocationEnd table 72) (capacity * allocationEnd 0 keyLength) table 32 htabNewValuesAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain32
  have nt : ofString "keys" ≠ ofString "t" := by decide
  have nc : ofString "keys" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_values_allocation_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain40) (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_keys_allocation,run]
  rw [tail]
  exact ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 6; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩


#print axioms evaluate_htabNew_used_allocation_of_safe_plan
#print axioms evaluate_htabNew_values_allocation_of_safe_plan
#print axioms evaluate_htabNew_keys_allocation_of_safe_plan
end InitECandidate.Runtime

import InitECandidate.Runtime.HashNewHeaderCallHeap
import InitECandidate.Runtime.HashNewHeaderSafePlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_htabNew_zero_tail_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedBody = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd pointer (capacity * 8)) (capacity * 8)))) := by
  obtain ⟨ready,run,empty,_,cost,remaining,locals,globals,postCode,addresses,endian⟩ :=
    evaluate_htabNew_zero_prefix_of_safe_plan state table keyLength capacity htabNewAfterZero code (by omega)
      pointerBound tableAligned fullSafe tableLocal usedLocal capLocal domain48 wordDomain byteDomain
  obtain ⟨post,tail,clock,lastCode,lastAddresses,lastEndian,counts⟩ :=
    evaluate_htabNew_order_tail ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
  obtain ⟨checked,checkedRun,_,_,_,_,checkedHeap,_⟩ :=
    evaluate_htabNew_order_tail_heap ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
  have equal : post = checked := congrArg Prod.snd (tail.symm.trans checkedRun)
  refine ⟨post,?_,?_,by omega,by omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,(by rw [equal]; exact checkedHeap)⟩
  · rw [source_htabNew_zero_prefix,run,tail]
  · rw [counts]
    · exact empty
    · intro index inside
      exact ⟨htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 56 (by decide) index inside,
        htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 64 (by decide) index inside⟩


/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_htabNew_used_allocation_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
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
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,lastHeap⟩ :=
    evaluate_htabNew_zero_tail_heap_of_safe_plan entered (allocationEnd (htabNewUsed table keyLength capacity) capacity)
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
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap⟩


/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_htabNew_values_allocation_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
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
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,lastHeap⟩ :=
    evaluate_htabNew_used_allocation_heap_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_values_allocation,run]
  rw [tail]
  exact ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 5; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap⟩


/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_htabNew_keys_allocation_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
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
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,lastHeap⟩ :=
    evaluate_htabNew_values_allocation_heap_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain40) (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_keys_allocation,run]
  rw [tail]
  exact ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 6; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap⟩


/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_source_htabNew_header_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 7 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) =
        (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 7 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) ∧
      post.memory (table + 0) = .word keyLength ∧
      post.memory (table + 8) = .word (allocationEnd 0 keyLength) ∧
      post.memory (table + 16) = .word capacity ∧
      post.memory (table + 24) = .word 0 ∧
      post.memory (table + 32) = .word (allocationEnd table 72) ∧
      post.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      post.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      post.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      post.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) := by
  have plan := fullSafe
  obtain ⟨guard,finish,restSafe⟩ := plan
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 72] =
        some [.val (.word (72 : BitVec 64))] := by rfl
  obtain ⟨allocated,_,clock,_,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state (.const 72) table 72 arguments code (by omega) heap guard finish
  let bound := setVarHOLFinite (ofString "t") (.val (.word table)) allocated
  have nt : ofString "t" ≠ ofString "key_len" := by decide
  have nc : ofString "t" ≠ ofString "cap" := by decide
  have st : ofString "stride" ≠ ofString "t" := by decide
  have sc : ofString "stride" ≠ ofString "cap" := by decide
  have t : bound.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have k : bound.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,locals] using keyLocal
  have c : bound.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have domain : ∀ offset : Nat, offset ≤ 64 → bound.memaddrs (table + BitVec.ofNat 64 offset) := by
    simpa only [bound,setVarHOLFinite,addresses] using headerDomain
  have prefixRun := evaluate_htabNew_stride_header bound table keyLength capacity htabNewAfterHeader t k c
    (domain 0 (by decide)) (domain 8 (by decide)) (domain 16 (by decide)) (domain 24 (by decide))
  let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) bound
  let initialized := htabNewHeaderPost entered table keyLength (allocationEnd 0 keyLength) capacity
  have initializedClock : initialized.clock = state.clock - 1 := clock
  have it : initialized.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,st] using t
  have ic : initialized.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,sc] using c
  have stride : initialized.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))) := by
    simp [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have ih : initialized.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd table 72))) := by
    change allocated.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,keysField,valuesField,usedField,orderField,reverseField,frame⟩ :=
    evaluate_htabNew_keys_allocation_frame_of_safe_plan initialized table keyLength capacity (postCode.trans code) (by omega)
      ih restSafe pointerBound tableAligned fullSafe it ic stride
      (domain 32 (by decide)) (domain 40 (by decide)) (domain 48 (by decide))
      (domain 56 (by decide)) (domain 64 (by decide))
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using wordDomain)
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using byteDomain)
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,checkedHeap⟩ :=
    evaluate_htabNew_keys_allocation_heap_of_safe_plan initialized table keyLength capacity (postCode.trans code) (by omega)
      ih restSafe pointerBound tableAligned fullSafe it ic stride
      (domain 32 (by decide)) (domain 40 (by decide)) (domain 48 (by decide))
      (domain 56 (by decide)) (domain 64 (by decide))
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using wordDomain)
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using byteDomain)
  have equal : post = checked := congrArg Prod.snd (tail.symm.trans checkedRun)
  have lastHeap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
    rw [equal]; exact checkedHeap

  rw [source_htabNew_header,decl]
  rw [prefixRun]
  dsimp only
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 7; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap,?_,?_,?_,?_,keysField,valuesField,usedField,orderField,reverseField⟩
  · have preserved : post.memory (table + 0) = initialized.memory (table + 0) := frame 0 (by simp)
    change post.memory (table + 0) = _
    rw [preserved]
    exact (htabNewHeaderPost_fields entered table keyLength (allocationEnd 0 keyLength) capacity).1
  · have preserved : post.memory (table + 8) = initialized.memory (table + 8) := frame 8 (by simp)
    change post.memory (table + 8) = _
    rw [preserved]
    exact (htabNewHeaderPost_fields entered table keyLength (allocationEnd 0 keyLength) capacity).2.1
  · have preserved : post.memory (table + 16) = initialized.memory (table + 16) := frame 16 (by simp)
    change post.memory (table + 16) = _
    rw [preserved]
    exact (htabNewHeaderPost_fields entered table keyLength (allocationEnd 0 keyLength) capacity).2.2.1
  · have preserved : post.memory (table + 24) = initialized.memory (table + 24) := frame 24 (by simp)
    change post.memory (table + 24) = _
    rw [preserved]
    exact (htabNewHeaderPost_fields entered table keyLength (allocationEnd 0 keyLength) capacity).2.2.2.1



/-- The actual safe constructor plan determines the final heap frontier,
while retaining emptiness and the established header fields. -/
theorem evaluate_htabNew_header_call_and_declaration_heap_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) ∧
      ready.memory (table + 0) = .word keyLength ∧
      ready.memory (table + 8) = .word (allocationEnd 0 keyLength) ∧
      ready.memory (table + 16) = .word capacity ∧
      ready.memory (table + 24) = .word 0 ∧
      ready.memory (table + 32) = .word (allocationEnd table 72) ∧
      ready.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      ready.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      ready.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "cap" ≠ ofString "key_len" := by decide
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,empty,cost,remaining,postCode,addresses,endian,heapAfter,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField⟩ :=
    evaluate_source_htabNew_header_heap_of_safe_plan entry table keyLength capacity code (by change capacity.toNat + 7 ≤ state.clock - 1; omega)
      heap pointerBound tableAligned fullSafe keyLocal capLocal headerDomain wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) keyLength capacity (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word table))) .one = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word table)) post arguments lookup (by omega) body shapeOk
  refine ⟨{post with locals := state.locals},call,empty,?_,?_,rfl,postCode,addresses,endian,heapAfter,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,?_⟩
  · change state.clock ≤ post.clock + capacity.toNat + 8
    change state.clock - 1 ≤ post.clock + capacity.toNat + 7 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_new") .one .one
      [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
      (sourceFunctionBody Guest.guestFn_htab_new) continuation callee (.val (.word table)) arguments lookup
      (by omega) body remaining shapeOk shapeOk


#print axioms evaluate_htabNew_zero_tail_heap_of_safe_plan
#print axioms evaluate_htabNew_used_allocation_heap_of_safe_plan
#print axioms evaluate_htabNew_values_allocation_heap_of_safe_plan
#print axioms evaluate_htabNew_keys_allocation_heap_of_safe_plan
#print axioms evaluate_source_htabNew_header_heap_of_safe_plan
#print axioms evaluate_htabNew_header_call_and_declaration_heap_of_safe_plan
end InitECandidate.Runtime

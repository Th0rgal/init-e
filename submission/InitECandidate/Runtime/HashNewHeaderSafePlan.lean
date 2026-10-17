import InitECandidate.Runtime.HashNewHeaderCall
import InitECandidate.Runtime.HashNewZeroSafePlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_zero_prefix_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 1 ≤ state.clock)
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (headerDomain : state.memaddrs (table + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state (htabNewZeroPrefix continuation) = evaluateHOLFiniteState ready continuation ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      state.clock ≤ ready.clock + capacity.toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ∀ offset : Nat, offset ≤ 40 → ready.memory (table + BitVec.ofNat 64 offset) =
        state.memory (table + BitVec.ofNat 64 offset) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word (htabNewUsed table keyLength capacity)),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  have safeCopy := fullSafe
  obtain ⟨_,_,_,keysFinish,valuesRequest,valuesFinish,usedRequest,_⟩ := safeCopy
  have usedEnd := allocationGuard_sum_bound (htabNewUsed table keyLength capacity) capacity valuesFinish usedRequest
  have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
  have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
  change (htabNewUsed table keyLength capacity).toNat % 8 = 0 at usedAligned
  have bounds := And.intro usedEnd usedAligned
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,empty,frame⟩ :=
    evaluate_memzero_aligned_call_with_frame state _ _ (htabNewUsed table keyLength capacity) capacity arguments code ticks
      bounds.1 bounds.2 wordDomain byteDomain
  have t : post.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [locals]; exact tableLocal
  have u : post.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    rw [locals]; exact usedLocal
  have store := evaluate_store_word post (table + 48) (htabNewUsed table keyLength capacity)
    _ (.var .local (ofString "used")) (eval_hashLocalAddress post (ofString "t") table 48 t) u
    (by rw [domain]; exact headerDomain)
  let ready := sourceWriteWord post (table + 48) (htabNewUsed table keyLength capacity)
  refine ⟨ready,?_,?_,?_,cost,remaining,locals,globals,postCode,domain,endian,?_⟩
  · unfold htabNewZeroPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store]
  · change hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord post (table + BitVec.ofNat 64 48) _) _) = 0
    rw [htabNew_header_store_preserves_count_of_safe_plan post table keyLength capacity _ pointerBound tableAligned fullSafe 48 (by decide)]
    exact empty
  · simp [ready,sourceWriteWord]

  · intro offset small
    have layout := htabNew_insertion_layout_of_safe_plan table keyLength capacity pointerBound fullSafe
    dsimp only at layout
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    have address48 : (table + (48 : BitVec 64)).toNat = table.toNat + 48 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 48 < 2 ^ 64; omega)]
      rfl
    have separate : table + BitVec.ofNat 64 offset ≠ table + 48 := by
      intro same
      have equal := congrArg BitVec.toNat same
      rw [address,address48] at equal
      omega
    have outside : (table + BitVec.ofNat 64 offset).toNat < (htabNewUsed table keyLength capacity).toNat := by
      omega
    have protectedWord := memcpy_interval_separate (htabNewUsed table keyLength capacity) capacity
      (table + BitVec.ofNat 64 offset) bounds.2 bounds.1 (Or.inl outside)
    change (sourceWriteWord post (table + 48) _).memory _ = _
    simp only [sourceWriteWord,if_neg separate]
    exact frame _ (fun byte inside => (protectedWord byte inside).1)
      (fun byte inside => (protectedWord byte inside).2)


/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_zero_tail_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      post.memory (table + 56) = .word pointer ∧
      post.memory (table + 64) = .word (allocationEnd pointer (capacity * 8)) ∧
      ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), post.memory (table + BitVec.ofNat 64 offset) =
        state.memory (table + BitVec.ofNat 64 offset) := by
  obtain ⟨ready,run,empty,stored,cost,remaining,locals,globals,postCode,addresses,endian,frame⟩ :=
    evaluate_htabNew_zero_prefix_frame_of_safe_plan state table keyLength capacity htabNewAfterZero code (by omega)
      pointerBound tableAligned fullSafe tableLocal usedLocal capLocal domain48 wordDomain byteDomain
  obtain ⟨post,tail,clock,lastCode,lastAddresses,lastEndian,counts⟩ :=
    evaluate_htabNew_order_tail ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
  obtain ⟨framed,frameRun,_,_,_,_,memory⟩ :=
    evaluate_htabNew_order_tail_memory ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
  have same : post = framed := congrArg Prod.snd (tail.symm.trans frameRun)
  have postMemory : post.memory = (sourceWriteWord (sourceWriteWord ready (table + 56) pointer)
      (table + 64) (allocationEnd pointer (capacity * 8))).memory := by rw [same]; exact memory
  refine ⟨post,?_,?_,by omega,by omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_,?_,?_,?_⟩
  · rw [source_htabNew_zero_prefix,run,tail]
  · rw [counts]
    · exact empty
    · intro index inside
      exact ⟨htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 56 (by decide) index inside,
        htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 64 (by decide) index inside⟩

  · rw [postMemory]
    simpa [sourceWriteWord] using stored
  · rw [postMemory]
    simp [sourceWriteWord]
  · rw [postMemory]
    simp [sourceWriteWord]
  · intro offset member
    have bound : offset ≤ 40 := by
      simp at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have preserved := frame offset bound
    rw [postMemory]
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [sourceWriteWord] using preserved


/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_used_allocation_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      post.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      post.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), post.memory (table + BitVec.ofNat 64 offset) =
        state.memory (table + BitVec.ofNat 64 offset) := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "cap")] =
        some [.val (.word capacity)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal]
  obtain ⟨allocated,_,clock,memory,locals,postCode,addresses,_,endian,globals,decl⟩ :=
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
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,usedField,orderField,reverseField,frame⟩ :=
    evaluate_htabNew_zero_tail_frame_of_safe_plan entered (allocationEnd (htabNewUsed table keyLength capacity) capacity)
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
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 4; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,usedField,orderField,reverseField,?_⟩
  intro offset member
  have preserved := frame offset member
  change post.memory _ = _
  change post.memory _ = allocated.memory _ at preserved
  rw [preserved,memory]



/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_values_allocation_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      post.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      post.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      post.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      ∀ offset ∈ ([0,8,16,24,32] : List Nat), post.memory (table + BitVec.ofNat 64 offset) =
        state.memory (table + BitVec.ofNat 64 offset) := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,memory,stored,heapNext,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "vals") (ofString "t") _
      (htabNewValues table keyLength capacity) (capacity * 8) table 40 htabNewUsedAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain40
  have nt : ofString "vals" ≠ ofString "t" := by decide
  have nc : ofString "vals" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,usedField,orderField,reverseField,frame⟩ :=
    evaluate_htabNew_used_allocation_frame_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_values_allocation,run]
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 5; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_,usedField,orderField,reverseField,?_⟩
  · have preserved := frame 40 (by simp)
    change post.memory (table + 40) = _
    simpa using preserved.trans stored
  · intro offset member
    have memberAll : offset ∈ ([0,8,16,24,32,40] : List Nat) := by
      simp at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
    have preserved := frame offset memberAll
    change post.memory _ = _
    rw [preserved,memory]
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [sourceWriteWord]



/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_keys_allocation_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.memory (table + 32) = .word (allocationEnd table 72) ∧
      post.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      post.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      post.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      post.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      ∀ offset ∈ ([0,8,16,24] : List Nat), post.memory (table + BitVec.ofNat 64 offset) =
        state.memory (table + BitVec.ofNat 64 offset) := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * allocationEnd 0 keyLength))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,memory,stored,heapNext,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "keys") (ofString "t") _
      (allocationEnd table 72) (capacity * allocationEnd 0 keyLength) table 32 htabNewValuesAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain32
  have nt : ofString "keys" ≠ ofString "t" := by decide
  have nc : ofString "keys" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,valuesField,usedField,orderField,reverseField,frame⟩ :=
    evaluate_htabNew_values_allocation_frame_of_safe_plan ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe pointerBound tableAligned fullSafe t c
      (by rw [addresses]; exact domain40) (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_keys_allocation,run]
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 6; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_,valuesField,usedField,orderField,reverseField,?_⟩
  · have preserved := frame 32 (by simp)
    change post.memory (table + 32) = _
    simpa using preserved.trans stored
  · intro offset member
    have memberAll : offset ∈ ([0,8,16,24,32] : List Nat) := by
      simp at member
      rcases member with rfl | rfl | rfl | rfl <;> simp
    have preserved := frame offset memberAll
    change post.memory _ = _
    rw [preserved,memory]
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [sourceWriteWord]



/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_source_htabNew_header_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  rw [source_htabNew_header,decl]
  rw [prefixRun]
  dsimp only
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 7; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_,?_,?_,?_,keysField,valuesField,usedField,orderField,reverseField⟩
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



/-- The original constructor preserves and establishes header fields using
its actual safe allocation plan, without a conservative heap reserve. -/
theorem evaluate_htabNew_header_call_and_declaration_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  obtain ⟨post,body,empty,cost,remaining,postCode,addresses,endian,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField⟩ :=
    evaluate_source_htabNew_header_of_safe_plan entry table keyLength capacity code (by change capacity.toNat + 7 ≤ state.clock - 1; omega)
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
  refine ⟨{post with locals := state.locals},call,empty,?_,?_,rfl,postCode,addresses,endian,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,?_⟩
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


#print axioms evaluate_htabNew_zero_prefix_frame_of_safe_plan
#print axioms evaluate_htabNew_zero_tail_frame_of_safe_plan
#print axioms evaluate_htabNew_used_allocation_frame_of_safe_plan
#print axioms evaluate_htabNew_values_allocation_frame_of_safe_plan
#print axioms evaluate_htabNew_keys_allocation_frame_of_safe_plan
#print axioms evaluate_source_htabNew_header_of_safe_plan
#print axioms evaluate_htabNew_header_call_and_declaration_of_safe_plan
end InitECandidate.Runtime

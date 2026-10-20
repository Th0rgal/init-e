import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.ByteStorePrefixReach
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.MemzeroAlignedCall
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.OriginalAttemptWrapperCode
import Guest.Ast
/-! The actual `Guest.guestFn_payload_header` construction baseFacts.

Real source (`Guest/guest.pp.pnk`): load `pl` from `si+0`, load `raw` from `pl+0`,
`alloc 248` into `h`, `memzero(h, 248)`, stores, `alloc 32`/`alloc 8`, `keccak256(tmp,1,oh)`, more
allocations/stores, and finally `block_rlp_length(h, pl)`.

This module ties the spine to the real structural body by `rfl` identities and proves the first
construction prefix: the two loads and the actual `alloc 248` declaration call, ending immediately at
`memzero(h, 248)`, with the typed `pl`/`raw`/`h` locals, the advanced heap pointer and the preserved
domain and code. -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The statements of the actual `payload_header` function, indexed. -/
def actualPayloadHeaderAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_payload_header)

/-- Statement 0: `pl := load [si + 0]`. -/
theorem source_actual_payload_header_pl :
    actualPayloadHeaderAt 0 = .dec (ofString "pl") .one
      (.load .one (.op .add [.var .local (ofString "si"), .const (0#64)])) (actualPayloadHeaderAt 1) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 1: `raw := load [pl + 0]`. -/
theorem source_actual_payload_header_raw :
    actualPayloadHeaderAt 1 = .dec (ofString "raw") .one
      (.load .one (.op .add [.var .local (ofString "pl"), .const (0#64)])) (actualPayloadHeaderAt 2) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 2: the actual `alloc 248` declaration call. -/
theorem source_actual_payload_header_alloc :
    actualPayloadHeaderAt 2 = .decCall (ofString "h") .one (ofString "alloc") [(.const (248#64))]
      (actualPayloadHeaderAt 3) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 3 begins with the actual `memzero(h, 248)` call. -/
theorem source_actual_payload_header_memzero :
    actualPayloadHeaderAt 3 = .seq (.call (some (none,none)) (ofString "memzero")
      [.var .local (ofString "h"), .const (248#64)]) (actualPayloadHeaderAt 4) := by
  unfold actualPayloadHeaderAt
  rfl

#print axioms source_actual_payload_header_memzero

/-- Evaluating a one-word load from a typed local with a readable cell. -/
theorem actual_payload_header_eval_load_word {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (base offset value : BitVec 64)
    (entryLocal : state.locals.lookup name = some (.val (.word base)))
    (domain : state.memaddrs (base + offset)) (cell : state.memory (base + offset) = .word value) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local name, .const offset])) =
      (some (ValueHOL.val (HolWordLab.word value)) : Option (ValueHOL 64)) := by
  simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
    memLoadHOLExact,entryLocal,domain,cell]
#print axioms actual_payload_header_eval_load_word

/-- The typed entry facts of the actual construction prefix at the state just before `alloc 248`. -/
def ActualPayloadHeaderLoads (state post : PanSemStateFiniteExact 64 F) (pl raw : BitVec 64) : Prop :=
  post.locals.lookup (ofString "pl") = some (.val (.word pl)) ∧
  post.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
  post.globals = state.globals ∧ post.memory = state.memory ∧
  post.memaddrs = state.memaddrs ∧ post.code = state.code

/-- **The actual construction prefix through the real `alloc 248`.**  From the real entry: `pl := load
[si+0]`, `raw := load [pl+0]`, and the actual `alloc 248` declaration call, ending immediately at
`memzero(h, 248)`, with `h = pointer`, `pl`, `raw` typed, the heap advanced to
`allocationEnd pointer 248`, and the domain and code unchanged. -/
theorem actual_payload_header_prefix_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (budget : 2 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => post.locals.lookup (ofString "h") = some (.val (.word pointer)) ∧
        post.locals.lookup (ofString "pl") = some (.val (.word pl)) ∧
        post.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.memaddrs = state.memaddrs ∧ post.code = state.code) 2 (actualPayloadHeaderAt 3) := by
  have first : Reaches state (actualPayloadHeaderAt 0)
      (fun next => next = setVarHOLFinite (ofString "pl") (.val (.word pl)) state) 0
      (actualPayloadHeaderAt 1) := by
    rw [source_actual_payload_header_pl]
    apply reaches_dec
    intro value evaluated
    rw [actual_payload_header_eval_load_word state (ofString "si") si (0#64) pl siLocal siDomain siCell] at evaluated
    cases Option.some.inj evaluated
    exact ⟨pl,rfl,rfl⟩
  have second : Reaches (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)
      (actualPayloadHeaderAt 1)
      (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) 0 (actualPayloadHeaderAt 2) := by
    rw [source_actual_payload_header_raw]
    apply reaches_dec
    intro found evaluated
    rw [actual_payload_header_eval_load_word (setVarHOLFinite (ofString "pl") (.val (.word pl)) state) (ofString "pl") pl (0#64) raw
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simpa [setVarHOLFinite] using plDomain) (by simpa [setVarHOLFinite] using plCell)] at evaluated
    cases Option.some.inj evaluated
    exact ⟨raw,rfl,rfl⟩
  have loads : Reaches state (actualPayloadHeaderAt 0)
      (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) 0 (actualPayloadHeaderAt 2) :=
    reaches_trans state (actualPayloadHeaderAt 0) (actualPayloadHeaderAt 1) (actualPayloadHeaderAt 2)
      _ _ 0 0 first (fun E equal => equal ▸ second)
  refine reaches_trans state (actualPayloadHeaderAt 0) (actualPayloadHeaderAt 2) (actualPayloadHeaderAt 3)
    _ _ 0 2 loads ?_
  intro mid typed
  subst typed
  rw [source_actual_payload_header_alloc]
  have code2 : (setVarHOLFinite (ofString "raw") (.val (.word raw))
      (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).code = originalRuntimeCode := by
    simpa [setVarHOLFinite] using code
  have heap2 : (setVarHOLFinite (ofString "raw") (.val (.word raw))
      (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).globals.lookup (ofString "heap_ptr") =
      some (.val (.word pointer)) := by
    simpa [setVarHOLFinite] using heapGlobal
  have arguments : evalListHOLFinite (setVarHOLFinite (ofString "raw") (.val (.word raw))
      (setVarHOLFinite (ofString "pl") (.val (.word pl)) state))
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [(.const (248#64))] =
      (some [ValueHOL.val (HolWordLab.word (248#64))] : Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  refine bounded_decCall_reaches _ (ofString "h") (ofString "alloc") .one .one [(.const (248#64))]
    [ValueHOL.val (HolWordLab.word (248#64))] (sourceFunctionBody Guest.guestFn_alloc) (actualPayloadHeaderAt 3)
    (HolFiniteMapExact.empty.update (ofString "n",.val (.word (248#64)))) 1 _ arguments ?_ (by simpa [setVarHOLFinite] using budget) ?_ ?_
  · rw [pan_single_word_lookup _ (ofString "alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_alloc)
      (248#64) (by rw [code2]; exact originalRuntimeCode_allocation_lookup)]
  · have bound := evaluate_source_alloc_uniform_bounded
      (callEntryStateHOLFinite (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state))
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word (248#64))))) code2
      (by change 1 ≤ (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).clock - 1; simp [setVarHOLFinite]; omega)
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  · intro value post returned shapes
    have sizeLocal : (callEntryStateHOLFinite (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state))
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word (248#64))))).locals.lookup (ofString "n") =
        (some (ValueHOL.val (HolWordLab.word (248#64))) : Option (ValueHOL 64)) := by
      change (HolFiniteMapExact.empty.update (ofString "n",
        ValueHOL.val (HolWordLab.word (248#64)))).lookup (ofString "n") = _
      simp [HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨request,finish,valueEq,memory,domain,be,postCode,globals⟩ :=
      alloc_body_returned (callEntryStateHOLFinite (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state))
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word (248#64))))) post pointer (248#64)
        (by simpa [callEntryStateHOLFinite] using code2)
        (by simpa [callEntryStateHOLFinite] using heap2) sizeLocal value returned
    subst valueEq
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp only [setVarHOLFinite]
      rw [globals]
      simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp only [setVarHOLFinite]
      rw [domain]
      rfl
    · simp only [setVarHOLFinite]
      rw [postCode]
      rfl
#print axioms actual_payload_header_prefix_reaches
/-- **The actual construction prefix through `memzero(h, 248)`.**  Continuing the real entry: `alloc
248` then the actual `memzero(h, 248)` call, ending immediately at the first construction store, with
`h = pointer`, `pl`, `raw` typed, the zeroed 248-byte header prefix, the heap advanced to
`allocationEnd pointer 248`, and the domain and code unchanged. -/
theorem actual_payload_header_prefix_memzero {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + 248 ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (budget : 251 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ZeroBytePrefix post pointer 248 ∧
        post.locals.lookup (ofString "h") = some (.val (.word pointer)) ∧
        post.locals.lookup (ofString "pl") = some (.val (.word pl)) ∧
        post.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.memaddrs = state.memaddrs ∧ post.code = state.code) 251 (actualPayloadHeaderAt 4) := by
  rcases actual_payload_header_prefix_reaches state si pl raw pointer siLocal siDomain siCell
    plDomain plCell code heapGlobal (by omega) (by omega) with ⟨mid, typed, c1, c2, sc⟩ | ab
  · have sizeNat : (248#64).toNat = 248 := by decide
    have arguments : evalListHOLFinite mid
        (h := fun address => Classical.propDecidable (mid.memaddrs address))
        [.var .local (ofString "h"), .const (248#64)] =
        (some [ValueHOL.val (HolWordLab.word pointer), ValueHOL.val (HolWordLab.word (248#64))] :
          Option (List (ValueHOL 64))) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,typed.1]
    have stage : Reaches mid (actualPayloadHeaderAt 3)
        (fun post => ZeroBytePrefix post pointer 248 ∧
          post.locals.lookup (ofString "h") = some (.val (.word pointer)) ∧
          post.locals.lookup (ofString "pl") = some (.val (.word pl)) ∧
          post.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
          post.globals.lookup (ofString "heap_ptr") =
            some (.val (.word (allocationEnd pointer (248#64)))) ∧
          post.memaddrs = state.memaddrs ∧ post.code = state.code) 249
        (actualPayloadHeaderAt 4) := by
      rw [source_actual_payload_header_memzero]
      have codeMid : mid.code = originalRuntimeCode := by rw [typed.2.2.2.2.2]; exact code
      obtain ⟨post, run, zeroed, spent, kept, globals, postCode, domain, be, locals, occupied⟩ :=
        evaluate_memzero_aligned_call mid (.var .local (ofString "h")) (.const (248#64)) pointer (248#64)
          arguments codeMid (by omega) fits aligned
          (fun offset below => by rw [typed.2.2.2.2.1]; exact wordDomain offset below)
          (fun offset below => by rw [typed.2.2.2.2.1]; exact byteDomain offset below)
      refine reaches_seq mid (.call (some (none,none)) (ofString "memzero")
        [.var .local (ofString "h"), .const (248#64)]) (actualPayloadHeaderAt 4) 249 _ ?_
      refine Or.inl ⟨post,⟨zeroed,?_,?_,?_,?_,?_,?_⟩,by omega,by omega,run⟩
      · rw [locals]; exact typed.1
      · rw [locals]; exact typed.2.1
      · rw [locals]; exact typed.2.2.1
      · rw [globals]; exact typed.2.2.2.1
      · rw [domain]; exact typed.2.2.2.2.1
      · rw [postCode]; exact typed.2.2.2.2.2
    rcases stage with ⟨post, facts, s1, s2, sc2⟩ | ab2
    · refine Or.inl ⟨post, facts, ?_, ?_, scoped_trans sc sc2⟩
      · show state.clock ≤ post.clock + 251
        omega
      · show post.clock ≤ state.clock
        omega
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 2 251 (by omega) ab)
#print axioms actual_payload_header_prefix_memzero

/-- Statement 4 is the actual store `h[0] := 1`. -/
theorem source_actual_payload_header_store_zero :
    actualPayloadHeaderAt 4 = .seq (.store (.op .add [.var .local (ofString "h"), .const (0#64)]) (.const (1#64)))
      (actualPayloadHeaderAt 5) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 5 is the actual store `h[8] := raw + 0`. -/
theorem source_actual_payload_header_store_raw :
    actualPayloadHeaderAt 5 = .seq (.store (.op .add [.var .local (ofString "h"), .const (8#64)])
      (.op .add [.var .local (ofString "raw"), .const (0#64)])) (actualPayloadHeaderAt 6) := by
  unfold actualPayloadHeaderAt
  rfl

/-- A `local + constant` address expression evaluates to the shifted word. -/
theorem actual_payload_header_eval_word_add {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (base offset : BitVec 64) (entryLocal : state.locals.lookup name = some (.val (.word base))) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local name, .const offset]) =
      (some (ValueHOL.val (HolWordLab.word (base + offset))) : Option (ValueHOL 64)) := by
  simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
    entryLocal]

/-- A word constant evaluates to itself. -/
theorem actual_payload_header_eval_word_const {F : Type} (state : PanSemStateFiniteExact 64 F) (k : BitVec 64) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) (.const k) =
      (some (ValueHOL.val (HolWordLab.word k)) : Option (ValueHOL 64)) := by
  simp [evalHOLExact]

#print axioms actual_payload_header_eval_word_add
#print axioms actual_payload_header_eval_word_const

/-- One actual word store, from typed local and cell premises only: the address and value premises of
`evaluate_store_word` are discharged here with the explicit `@evalHOLExact` form, so call sites never
rebuild the evaluation instance. -/
theorem actual_payload_header_store_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (base offset : BitVec 64) (stored : BitVec 64)
    (entryLocal : state.locals.lookup name = some (.val (.word base)))
    (domain : state.memaddrs (base + offset)) :
    evaluateHOLFiniteState state (.store (.op .add [.var .local name, .const offset]) (.const stored)) =
      (none, sourceWriteWord state (base + offset) stored) := by
  exact evaluate_store_word state (base + offset) stored _ _
    (actual_payload_header_eval_word_add state name base offset entryLocal)
    (actual_payload_header_eval_word_const state stored) domain

/-- One actual word store whose value expression is a `local + constant`. -/
theorem actual_payload_header_store_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination name : MlS) (base valueBase offset valueOffset : BitVec 64)
    (destinationLocal : state.locals.lookup destination = some (.val (.word base)))
    (valueLocal : state.locals.lookup name = some (.val (.word valueBase)))
    (domain : state.memaddrs (base + offset)) :
    evaluateHOLFiniteState state (.store (.op .add [.var .local destination, .const offset])
      (.op .add [.var .local name, .const valueOffset])) =
      (none, sourceWriteWord state (base + offset) (valueBase + valueOffset)) := by
  exact evaluate_store_word state (base + offset) (valueBase + valueOffset) _ _
    (actual_payload_header_eval_word_add state destination base offset destinationLocal)
    (actual_payload_header_eval_word_add state name valueBase valueOffset valueLocal) domain

#print axioms actual_payload_header_store_word
#print axioms actual_payload_header_store_local

/-- The construction facts at a point of the actual header baseFacts. -/
def ActualPayloadHeaderPrefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) : Prop :=
  post.locals.lookup (ofString "pl") = some (.val (.word pl)) ∧
  post.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
  post.locals.lookup (ofString "h") = some (.val (.word pointer)) ∧
  post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
  post.memaddrs = state.memaddrs ∧ post.code = state.code

/-- A header store keeps every construction fact: stores change only memory. -/
theorem ActualPayloadHeaderPrefix.write {F : Type} {state mid : PanSemStateFiniteExact 64 F}
    {pl raw pointer heap address value : BitVec 64}
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap) :
    ActualPayloadHeaderPrefix state (sourceWriteWord mid address value) pl raw pointer heap := by
  obtain ⟨plLocal,rawLocal,hLocal,heapLocal,domain,code⟩ := facts
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [sourceWriteWord] using plLocal
  · simpa [sourceWriteWord] using rawLocal
  · simpa [sourceWriteWord] using hLocal
  · simpa [sourceWriteWord] using heapLocal
  · simpa [sourceWriteWord] using domain
  · simpa [sourceWriteWord] using code

#print axioms ActualPayloadHeaderPrefix.write

/-- **The actual construction prefix through both header stores.**  Continuing the real entry after
`memzero(h, 248)`: the actual stores `h[0] := 1` and `h[8] := raw + 0`, ending immediately at the
actual `alloc 32` for `oh`. -/
theorem actual_payload_header_prefix_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + 248 ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (budget : 251 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd pointer (248#64)))
      251 (actualPayloadHeaderAt 6) := by
  rcases actual_payload_header_prefix_memzero state si pl raw pointer siLocal siDomain siCell plDomain
    plCell code heapGlobal aligned fits wordDomain byteDomain budget with ⟨mid, facts, c1, c2, sc⟩ | ab
  · obtain ⟨zeroed,hLocal,plLocal,rawLocal,heapLocal,domain,codeMid⟩ := facts
    have storeZero : Reaches mid (actualPayloadHeaderAt 4)
        (fun post => post = sourceWriteWord mid (pointer + (0#64)) (1#64)) 0 (actualPayloadHeaderAt 5) := by
      rw [source_actual_payload_header_store_zero]
      refine reaches_seq mid (.store (.op .add [.var .local (ofString "h"), .const (0#64)]) (.const (1#64)))
        (actualPayloadHeaderAt 5) 0 _ ?_
      refine Or.inl ⟨sourceWriteWord mid (pointer + (0#64)) (1#64),rfl,by simp [sourceWriteWord],
        by simp [sourceWriteWord],?_⟩
      exact actual_payload_header_store_word mid (ofString "h") pointer (0#64) (1#64) hLocal
        (by rw [domain]; exact wordDomain 0 (by omega))
    have storeRaw : Reaches (sourceWriteWord mid (pointer + (0#64)) (1#64)) (actualPayloadHeaderAt 5)
        (fun post => post = sourceWriteWord (sourceWriteWord mid (pointer + (0#64)) (1#64))
          (pointer + (8#64)) (raw + (0#64))) 0 (actualPayloadHeaderAt 6) := by
      rw [source_actual_payload_header_store_raw]
      refine reaches_seq (sourceWriteWord mid (pointer + (0#64)) (1#64))
        (.store (.op .add [.var .local (ofString "h"), .const (8#64)])
          (.op .add [.var .local (ofString "raw"), .const (0#64)])) (actualPayloadHeaderAt 6) 0 _ ?_
      refine Or.inl ⟨_,rfl,by simp [sourceWriteWord],by simp [sourceWriteWord],?_⟩
      exact actual_payload_header_store_local (sourceWriteWord mid (pointer + (0#64)) (1#64))
        (ofString "h") (ofString "raw") pointer raw (8#64) (0#64)
        (by change mid.locals.lookup (ofString "h") = some (.val (.word pointer)); exact hLocal)
        (by change mid.locals.lookup (ofString "raw") = some (.val (.word raw)); exact rawLocal)
        (by change mid.memaddrs (pointer + (8#64)); rw [domain]; exact wordDomain 8 (by omega))
    have chain : Reaches mid (actualPayloadHeaderAt 4)
        (fun post => post = sourceWriteWord (sourceWriteWord mid (pointer + (0#64)) (1#64))
          (pointer + (8#64)) (raw + (0#64))) 0 (actualPayloadHeaderAt 6) :=
      reaches_trans mid (actualPayloadHeaderAt 4) (actualPayloadHeaderAt 5) (actualPayloadHeaderAt 6) _ _
        0 0 storeZero (fun E equal => equal ▸ storeRaw)
    rcases chain with ⟨post, equal, d1, d2, sc2⟩ | ab2
    · subst equal
      refine Or.inl ⟨_,?_,by omega,by omega,scoped_trans sc sc2⟩
      exact ActualPayloadHeaderPrefix.write (ActualPayloadHeaderPrefix.write
        ⟨plLocal,rawLocal,hLocal,heapLocal,domain,codeMid⟩)
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 251 251 (by omega) ab)
#print axioms actual_payload_header_prefix_stores

/-- Statement 6 is the actual `alloc 32` that produces `oh`. -/
theorem source_actual_payload_header_alloc_output :
    actualPayloadHeaderAt 6 = .decCall (ofString "oh") .one (ofString "alloc") [(.const (32#64))]
      (actualPayloadHeaderAt 7) := by
  unfold actualPayloadHeaderAt
  rfl

/-- A two-tick actual `alloc` declaration step, uniformly bounded, with the returned pointer bound to
`name`: every successful return advances the heap pointer to `allocationEnd heap size` and preserves
memory, domain and code. -/
theorem actual_payload_header_alloc_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (size heap : BitVec 64) (continuation : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : s.code = originalRuntimeCode) (budget : 2 ≤ s.clock)
    (property : ∀ post : PanSemStateFiniteExact 64 F,
      post.memory = s.memory → post.memaddrs = s.memaddrs → post.code = s.code →
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap size))) s).globals →
      P (setVarHOLFinite name (.val (.word heap)) {post with locals := s.locals})) :
    Reaches s (.decCall name .one (ofString "alloc") [(.const size)] continuation) P 2 continuation := by
  have arguments : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [(.const size)] = (some [ValueHOL.val (HolWordLab.word size)] : Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  refine bounded_decCall_reaches s name (ofString "alloc") .one .one [(.const size)]
    [ValueHOL.val (HolWordLab.word size)] (sourceFunctionBody Guest.guestFn_alloc) continuation
    (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))) 1 P arguments ?_ budget ?_ ?_
  · rw [pan_single_word_lookup _ (ofString "alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_alloc)
      size (by rw [code]; exact originalRuntimeCode_allocation_lookup)]
  · have bound := evaluate_source_alloc_uniform_bounded
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))) code
      (by change 1 ≤ s.clock - 1; omega)
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  · intro value post returned shapes
    have sizeLocal : (callEntryStateHOLFinite s
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))).locals.lookup (ofString "n") =
        (some (ValueHOL.val (HolWordLab.word size)) : Option (ValueHOL 64)) := by
      change (HolFiniteMapExact.empty.update (ofString "n",
        ValueHOL.val (HolWordLab.word size))).lookup (ofString "n") = _
      simp [HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨request,finish,valueEq,memory,domain,be,postCode,globals⟩ :=
      alloc_body_returned (callEntryStateHOLFinite s
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))) post heap size
        (by simpa [callEntryStateHOLFinite] using code)
        (by simpa [callEntryStateHOLFinite] using heapGlobal) sizeLocal value returned
    subst valueEq
    exact property post memory domain postCode globals

#print axioms actual_payload_header_alloc_step

/-- Statement 7 is the actual `alloc 8` that produces `tmp`. -/
theorem source_actual_payload_header_alloc_tmp :
    actualPayloadHeaderAt 7 = .decCall (ofString "tmp") .one (ofString "alloc") [(.const (8#64))]
      (actualPayloadHeaderAt 8) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 8 is the actual `storeByte tmp := 192`. -/
theorem source_actual_payload_header_store_byte :
    actualPayloadHeaderAt 8 = .seq (.storeByte (.var .local (ofString "tmp")) (.const (192#64)))
      (actualPayloadHeaderAt 9) := by
  unfold actualPayloadHeaderAt
  rfl

/-- The next actual `alloc`, from a state that carries the construction facts. -/
theorem actual_payload_header_alloc_next {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (name : MlS) (size : BitVec 64) (continuation : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (namePl : ofString "pl" ≠ name) (nameRaw : ofString "raw" ≠ name) (nameH : ofString "h" ≠ name)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (.decCall name .one (ofString "alloc") [(.const size)] continuation)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd heap size) ∧
        post.locals.lookup name = some (.val (.word heap))) 2 continuation := by
  refine actual_payload_header_alloc_step mid name size heap continuation _ facts.2.2.2.1
    (by rw [facts.2.2.2.2.2]; exact code) (by omega) ?_
  intro post memory domain postCode globals
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
  · by_cases same : name = ofString "pl"
    · exact absurd same.symm namePl
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,facts.1]
  · by_cases same : name = ofString "raw"
    · exact absurd same.symm nameRaw
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,facts.2.1]
  · by_cases same : name = ofString "h"
    · exact absurd same.symm nameH
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,facts.2.2.1]
  · simp only [setVarHOLFinite]
    rw [globals]
    simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp only [setVarHOLFinite]
    rw [domain]
    exact facts.2.2.2.2.1
  · simp only [setVarHOLFinite]
    rw [postCode]
    exact facts.2.2.2.2.2
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- **The actual construction prefix through the `alloc 32` for `oh`.**  Continuing the real entry
after the two header stores: the actual `alloc 32` declaration call, ending immediately at the actual
`alloc 8` for `tmp`. -/
theorem actual_payload_header_prefix_output {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + 248 ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (budget : 253 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd pointer (248#64)) (32#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
      253 (actualPayloadHeaderAt 7) := by
  rcases actual_payload_header_prefix_stores state si pl raw pointer siLocal siDomain siCell plDomain
    plCell code heapGlobal aligned fits wordDomain byteDomain (by omega) with ⟨mid, facts, c1, c2, sc⟩ | ab
  · have allocSteps : Reaches mid (actualPayloadHeaderAt 6)
        (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd pointer (248#64)) (32#64)) ∧
          post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
        2 (actualPayloadHeaderAt 7) := by
      rw [source_actual_payload_header_alloc_output]
      refine actual_payload_header_alloc_step mid (ofString "oh") (32#64) (allocationEnd pointer (248#64))
        (actualPayloadHeaderAt 7) _ facts.2.2.2.1 (by rw [facts.2.2.2.2.2]; exact code) (by omega) ?_
      intro post memory domain postCode globals
      refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          facts.1]
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          facts.2.1]
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          facts.2.2.1]
      · simp only [setVarHOLFinite]
        rw [globals]
        simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simp only [setVarHOLFinite]
        rw [domain]
        exact facts.2.2.2.2.1
      · simp only [setVarHOLFinite]
        rw [postCode]
        exact facts.2.2.2.2.2
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rcases allocSteps with ⟨post, facts', a1, a2, asc⟩ | ab2
    · exact Or.inl ⟨post, facts', by omega, by omega, scoped_trans sc asc⟩
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 251 253 (by omega) ab)
#print axioms actual_payload_header_prefix_output

/-- **The actual construction prefix through `alloc 8` and `storeByte tmp := 192`.**  Continuing the
real entry: the actual `alloc 8` for `tmp` and the actual `storeByte tmp := 192`, ending immediately
at the actual `keccak256(tmp, 1, oh)` call, with `h`, `pl`, `raw`, `oh`, `tmp` typed, the heap at
`allocationEnd (allocationEnd (allocationEnd pointer 248) 32) 8`, and the domain and code unchanged. -/
theorem actual_payload_header_prefix_store_byte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + 248 ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (budget : 255 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") =
          some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64)))))
      255 (actualPayloadHeaderAt 9) := by
  rcases actual_payload_header_prefix_output state si pl raw pointer siLocal siDomain siCell plDomain
    plCell code heapGlobal aligned fits wordDomain byteDomain (by omega) with ⟨mid, facts, c1, c2, sc⟩ | ab
  · obtain ⟨baseFacts, ohLocal⟩ := facts
    have allocSteps : Reaches mid (actualPayloadHeaderAt 7)
        (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
            (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
          post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
          post.locals.lookup (ofString "tmp") =
            some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64)))))
        2 (actualPayloadHeaderAt 8) := by
      rw [source_actual_payload_header_alloc_tmp]
      refine actual_payload_header_alloc_step mid (ofString "tmp") (8#64)
        (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (actualPayloadHeaderAt 8) _
        baseFacts.2.2.2.1 (by rw [baseFacts.2.2.2.2.2]; exact code) (by omega) ?_
      intro post memory domain postCode globals
      refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          baseFacts.1]
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          baseFacts.2.1]
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          baseFacts.2.2.1]
      · simp only [setVarHOLFinite]
        rw [globals]
        simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simp only [setVarHOLFinite]
        rw [domain]
        exact baseFacts.2.2.2.2.1
      · simp only [setVarHOLFinite]
        rw [postCode]
        exact baseFacts.2.2.2.2.2
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          ohLocal]
      · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rcases allocSteps with ⟨mid2, ⟨baseFacts2, oh2, tmp2⟩, a1, a2, asc⟩ | ab2
    · have byteSteps : Reaches mid2 (actualPayloadHeaderAt 8)
          (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
              (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
            post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
            post.locals.lookup (ofString "tmp") =
              some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64)))))
          0 (actualPayloadHeaderAt 9) := by
        rw [source_actual_payload_header_store_byte]
        have step := evaluate_storeByte_reaches mid2 (.var .local (ofString "tmp")) (.const (192#64))
          (actualPayloadHeaderAt 9)
        rcases step with ⟨post, ⟨g,l,c,d⟩, s1, s2, ssc⟩ | ab3
        · refine Or.inl ⟨post,⟨?_,?_,?_⟩,by omega,by omega,ssc⟩
          · refine ⟨?_,?_,?_,?_,?_,?_⟩
            · rw [l]; exact baseFacts2.1
            · rw [l]; exact baseFacts2.2.1
            · rw [l]; exact baseFacts2.2.2.1
            · rw [g]; exact baseFacts2.2.2.2.1
            · rw [d]; exact baseFacts2.2.2.2.2.1
            · rw [c]; exact baseFacts2.2.2.2.2.2
          · rw [l]; exact oh2
          · rw [l]; exact tmp2
        · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab3
          exact Or.inr ⟨x, h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
      rcases byteSteps with ⟨post, facts', b1, b2, bsc⟩ | ab3
      · exact Or.inl ⟨post, facts', by omega, by omega, scoped_trans sc (scoped_trans asc bsc)⟩
      · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab3
        have ck := (scoped_trans sc asc).2.1
        exact Or.inr ⟨x, (scoped_trans sc asc).1.trans h1, h2, by omega, by omega,
          fun k => h5 (by omega)⟩
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 253 255 (by omega) ab)

end InitECandidate.Runtime

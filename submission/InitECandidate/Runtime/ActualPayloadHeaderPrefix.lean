import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.OriginalAttemptWrapperCode
import Guest.Ast
/-! The actual `Guest.guestFn_payload_header` construction prefix.

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
theorem eval_load_word {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (base offset value : BitVec 64)
    (entryLocal : state.locals.lookup name = some (.val (.word base)))
    (domain : state.memaddrs (base + offset)) (cell : state.memory (base + offset) = .word value) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local name, .const offset])) =
      (some (ValueHOL.val (HolWordLab.word value)) : Option (ValueHOL 64)) := by
  simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
    memLoadHOLExact,entryLocal,domain,cell]
#print axioms eval_load_word

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
    rw [eval_load_word state (ofString "si") si (0#64) pl siLocal siDomain siCell] at evaluated
    cases Option.some.inj evaluated
    exact ⟨pl,rfl,rfl⟩
  have second : Reaches (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)
      (actualPayloadHeaderAt 1)
      (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) 0 (actualPayloadHeaderAt 2) := by
    rw [source_actual_payload_header_raw]
    apply reaches_dec
    intro found evaluated
    rw [eval_load_word (setVarHOLFinite (ofString "pl") (.val (.word pl)) state) (ofString "pl") pl (0#64) raw
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
end InitECandidate.Runtime

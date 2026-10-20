import InitECandidate.Runtime.ActualPayloadHeaderExtraLength
import InitECandidate.Runtime.FourWordStoreMemoryFrame
import InitECandidate.Runtime.NodedbWindowGeometry
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.AllocationRoundNoWrap
import InitECandidate.Runtime.RunBoundedReaches

set_option maxHeartbeats 8000000

/-!
# Carrying the loader's extra-length cell through the actual header construction

The construction predicate `ActualPayloadHeaderPrefix` records the pointers, the memory domain and
the code, but deliberately says nothing about the contents of memory.  The extra length that the
actual construction copies into the header at statement 23 comes from the payload cell `pl + 24`,
which lives *below* the fresh header block, so every write of the construction -- the header
allocation, its `memzero`, the byte and word stores, the `keccak256` workspace and the test scratch
byte -- leaves it intact.  This module carries that single cell through the actual straight-line
construction, so that statement 23 can copy it into the header and the tail can keep it there.

The helper lemmas at the top are the frame facts for one actual word store, one actual four-limb
structure store and one byte store, plus the geometry of the header block that separates the watched
cell from every destination of the construction.
-/

namespace InitECandidate.Runtime

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A one-word store preserves the watched word when the destination is another cell. -/
theorem WatchWord.sourceWriteWord_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address stored watched value : BitVec 64) (separate : watched ≠ address)
    (watch : WatchWord state watched value) :
    WatchWord (Runtime.sourceWriteWord state address stored) watched value := by
  unfold WatchWord at watch ⊢
  unfold Runtime.sourceWriteWord
  change (if watched = address then HolWordLab.word stored else state.memory watched) =
    HolWordLab.word value
  rw [if_neg separate]
  exact watch

#print axioms WatchWord.sourceWriteWord_frame

/-- The natural value of a header cell `pointer + k` for a header below the memory cap. -/
theorem actual_payload_header_offset_nat (pointer : BitVec 64) (k : Nat)
    (cap : pointer.toNat ≤ 33806089496) (bound : k < 248) :
    (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k := by
  have offsetNat : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; have := pointer.isLt; omega),offsetNat]

#print axioms actual_payload_header_offset_nat

/-- Distinct header offsets are distinct header cells. -/
theorem actual_payload_header_offset_ne (pointer : BitVec 64) (a b : Nat)
    (cap : pointer.toNat ≤ 33806089496) (aBound : a < 248) (bBound : b < 248)
    (different : a ≠ b) :
    pointer + BitVec.ofNat 64 a ≠ pointer + BitVec.ofNat 64 b := by
  intro same
  have levels := congrArg BitVec.toNat same
  rw [actual_payload_header_offset_nat pointer a cap aBound,
    actual_payload_header_offset_nat pointer b cap bBound] at levels
  omega

#print axioms actual_payload_header_offset_ne

/-- The natural value of the loader's extra-length cell. -/
theorem actual_payload_header_pl_cell_nat (pl : BitVec 64) (bound : pl.toNat + 24 < 2^64) :
    (pl + (24#64)).toNat = pl.toNat + 24 := by
  have twenty : (24#64).toNat = 24 := by decide
  rw [BitVec.toNat_add_of_lt (by rw [twenty]; exact bound),twenty]

#print axioms actual_payload_header_pl_cell_nat

/-- **A store of a single evaluated word-lab changes only its own cell.**  The value's flattening is
one word whatever the payload is, so a store whose destination evaluates to another address leaves
the watched cell alone -- this covers loads, which can yield a byte payload as readily as a word. -/
theorem evaluate_store_val_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address watched : BitVec 64) (payload : HolWordLab 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value = some (.val payload))
    (separate : watched ≠ address) :
    (evaluateHOLFiniteState state (.store destination value)).2.memory watched =
      state.memory watched := by
  rw [evaluateHOLFiniteState_store,addressEval,valueEval]
  by_cases accessible : state.memaddrs address
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible,separate]
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible]

#print axioms evaluate_store_val_memory_frame

/-- An actual one-word load from a typed pointer local, given only the readability of its cell. -/
theorem actual_payload_header_eval_load_one {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (base offset : BitVec 64)
    (entryLocal : state.locals.lookup name = some (.val (.word base)))
    (domain : state.memaddrs (base + offset)) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local name, .const offset])) =
      (some (.val (state.memory (base + offset))) : Option (ValueHOL 64)) := by
  simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,entryLocal,
    memLoadHOLExact,domain]

#print axioms actual_payload_header_eval_load_one

/-- **A watched word survives one actual header store.**  The store is the actual
`h[k] := value` of the header construction: the destination is the header cell `pointer + k` and the
value is a word, so only that cell changes and the watched word elsewhere is untouched. -/
theorem actual_payload_header_store_step_strong_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (destination value : ExpHOL 64) (stored : BitVec 64) (tail : ProgHOL 64)
    (shape : actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (destShape : destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer heap)
    (valueShape : ∀ parsed, @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) value = some parsed →
      ∃ payload : HolWordLab 64, parsed = .val payload)
    (separate : watched ≠ pointer + BitVec.ofNat 64 k)
    (watch : WatchWord mid watched cell) :
    Reaches mid (actualPayloadHeaderAt index)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer heap ∧
        WatchWord post watched cell) 0 tail := by
  obtain ⟨baseFacts, frame⟩ := facts
  have addressEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) destination =
      some (.val (.word (pointer + BitVec.ofNat 64 k))) := by
    rw [destShape]
    exact actual_payload_header_eval_word_add mid (ofString "h") pointer (BitVec.ofNat 64 k)
      baseFacts.2.2.1
  rw [shape]
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · have frameMemory : memory watched = mid.memory watched := by
      have runMemory : (evaluateHOLFiniteState mid (.store destination value)).2.memory watched =
          mid.memory watched := by
        cases evaluated : @evalHOLExact 64 F _ mid.toExact
            (fun a => Classical.propDecidable (mid.memaddrs a)) value with
        | none =>
          simp only [evaluateHOLFiniteState_store,addressEval,evaluated] at run
          exact absurd (congrArg Prod.fst run) (by simp)
        | some parsed =>
          obtain ⟨payload,rfl⟩ := valueShape parsed evaluated
          exact evaluate_store_val_memory_frame mid destination value
            (pointer + BitVec.ofNat 64 k) watched payload addressEval evaluated separate
      rw [run] at runMemory
      exact runMemory
    refine Or.inl ⟨{mid with memory := memory},
      ⟨⟨baseFacts,frame.trans (HeapGlobalsFrame.of_globals (by rfl))⟩,?_⟩,by simp,by simp,run⟩
    show memory watched = .word cell
    rw [frameMemory]
    exact watch

#print axioms actual_payload_header_store_step_strong_watched

/-- **A watched word survives one actual header store of a four-limb structure.**  The header's
`h[64] := rStruct [..]` and `h[160] := bf` stores write four consecutive header words; a watched cell
that is none of those four survives. -/
theorem actual_payload_header_store_four_strong_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (destination value : ExpHOL 64)
    (first second third fourth : BitVec 64) (tail : ProgHOL 64)
    (shape : actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (destShape : destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer heap)
    (valueEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) value =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (apart0 : watched ≠ pointer + BitVec.ofNat 64 k)
    (apart8 : watched ≠ pointer + BitVec.ofNat 64 k + (8#64))
    (apart16 : watched ≠ pointer + BitVec.ofNat 64 k + (16#64))
    (apart24 : watched ≠ pointer + BitVec.ofNat 64 k + (24#64))
    (watch : WatchWord mid watched cell) :
    Reaches mid (actualPayloadHeaderAt index)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer heap ∧
        WatchWord post watched cell) 0 tail := by
  obtain ⟨baseFacts, frame⟩ := facts
  have addressEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) destination =
      some (.val (.word (pointer + BitVec.ofNat 64 k))) := by
    rw [destShape]
    exact actual_payload_header_eval_word_add mid (ofString "h") pointer (BitVec.ofNat 64 k)
      baseFacts.2.2.1
  rw [shape]
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · have frameMemory : memory watched = mid.memory watched := by
      have stored := evaluate_fourWordStore_memory_frame mid destination value
        (pointer + BitVec.ofNat 64 k) first second third fourth watched addressEval valueEval
        apart0 apart8 apart16 apart24
      rw [run] at stored
      exact stored
    refine Or.inl ⟨{mid with memory := memory},
      ⟨⟨baseFacts,frame.trans (HeapGlobalsFrame.of_globals (by rfl))⟩,?_⟩,by simp,by simp,run⟩
    show memory watched = .word cell
    rw [frameMemory]
    exact watch

#print axioms actual_payload_header_store_four_strong_watched

/-- **The stronger prefix with the loader's extra-length cell carried along.**  The two actual loads
and the actual header allocation cannot change memory at all, so the cell that held the extra length
before the construction still holds it after the allocation. -/
theorem actual_payload_header_strong_prefix_watched {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (si pl raw pointer extraLen : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (watch : WatchWord state (pl + (24#64)) extraLen)
    (budget : 2 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd pointer (248#64)) ∧ pointer.toNat + 248 ≤ 33806089496 ∧
        WatchWord post (pl + (24#64)) extraLen) 2 (actualPayloadHeaderAt 3) := by
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
    rw [actual_payload_header_eval_load_word (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)
      (ofString "pl") pl (0#64) raw
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simpa [setVarHOLFinite] using plDomain)
      (by simpa [setVarHOLFinite] using plCell)] at evaluated
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
    have capNat : (33806089496 : BitVec 64).toNat = 33806089496 := by decide
    have fits : pointer.toNat + 248 ≤ 33806089496 := by
      have le : (248#64).toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := BitVec.le_def.1 request
      have sub := BitVec.toNat_sub_of_le (x := (33806089496 : BitVec 64)) (y := pointer) (by
        show pointer.toNat ≤ (33806089496 : BitVec 64).toNat
        rw [capNat]; exact pointerBound)
      have sizeNat : (248#64).toNat = 248 := by decide
      rw [sub, capNat, sizeNat] at le
      omega
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,fits,?_⟩
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
    · intro name different
      simp only [setVarHOLFinite]
      rw [globals]
      by_cases hname : (ofString "heap_ptr" = name)
      · exact absurd hname.symm different
      · simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          hname,setVarHOLFinite,callEntryStateHOLFinite]
    · show (setVarHOLFinite (ofString "h") (.val (.word pointer))
        {post with locals := (setVarHOLFinite (ofString "raw") (.val (.word raw))
          (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).locals}).memory (pl + (24#64)) =
        HolWordLab.word extraLen
      have same : (setVarHOLFinite (ofString "h") (.val (.word pointer))
          {post with locals := (setVarHOLFinite (ofString "raw") (.val (.word raw))
            (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).locals}).memory = state.memory := by
        simp [setVarHOLFinite,memory,callEntryStateHOLFinite]
      rw [same]
      exact watch

#print axioms actual_payload_header_strong_prefix_watched


/-- **The stronger prefix through both header stores, watched.**  The actual `h[0] := 1` and
`h[8] := raw + 0` write header cells, so the loader's extra-length cell below the header survives. -/
theorem actual_payload_header_strong_stores_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer extraLen : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd pointer (248#64)))
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (watch : WatchWord mid (pl + (24#64)) extraLen) :
    Reaches mid (actualPayloadHeaderAt 4)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd pointer (248#64)) ∧ WatchWord post (pl + (24#64)) extraLen) 0
      (actualPayloadHeaderAt 6) := by
  rcases actual_payload_header_store_step_strong_watched state mid pl raw pointer
    (allocationEnd pointer (248#64)) (pl + (24#64)) extraLen 4 0 _ _ (1#64) (actualPayloadHeaderAt 5)
    source_actual_payload_header_store_zero rfl facts
    (by
      intro parsed evaluated
      exact ⟨_,Option.some.inj (evaluated.symm.trans (actual_payload_header_eval_word_const mid (1#64)))⟩)
    (actual_payload_header_pl_cell_word_separate pl pointer 0 below cap (by omega)) watch with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · rcases actual_payload_header_store_step_strong_watched state E pl raw pointer
      (allocationEnd pointer (248#64)) (pl + (24#64)) extraLen 5 8 _ _ (raw + (0#64))
      (actualPayloadHeaderAt 6) source_actual_payload_header_store_raw rfl pE.1
      (by
        intro parsed evaluated
        exact ⟨_,Option.some.inj (evaluated.symm.trans
          (actual_payload_header_eval_word_add E (ofString "raw") raw (0#64) pE.1.1.2.1))⟩)
      (actual_payload_header_pl_cell_word_separate pl pointer 8 below cap (by omega)) pE.2 with
      ⟨G, pG, d1, d2, sd⟩ | ab2
    · exact Or.inl ⟨G, pG, by omega, by omega, scoped_trans sc sd⟩
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr ab

#print axioms actual_payload_header_strong_stores_watched

/-- **The stronger prefix through the actual `alloc 32` for `oh`, watched.** -/
theorem actual_payload_header_strong_alloc_oh_watched {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer extraLen : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd pointer (248#64)))
    (code : state.code = originalRuntimeCode)
    (watch : WatchWord mid (pl + (24#64)) extraLen)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 6)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd pointer (248#64)) (32#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        WatchWord post (pl + (24#64)) extraLen ∧
        (allocationEnd (allocationEnd pointer (248#64)) (32#64)).toNat ≤ 33806089496) 2
      (actualPayloadHeaderAt 7) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_alloc_output]
  refine actual_payload_header_alloc_step_earned mid (ofString "oh") (32#64)
    (allocationEnd pointer (248#64)) (actualPayloadHeaderAt 7) _ baseFacts.2.2.2.1
    (by rw [baseFacts.2.2.2.2.2]; exact code) budget ?_
  intro post memory domain postCode globals floor
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_,?_,floor⟩
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
  · exact HeapGlobalsFrame.alloc state mid frame (allocationEnd pointer (248#64)) (32#64) post globals
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · show (setVarHOLFinite (ofString "oh") (.val (.word (allocationEnd pointer (248#64))))
      {post with locals := mid.locals}).memory (pl + (24#64)) = HolWordLab.word extraLen
    have same : (setVarHOLFinite (ofString "oh") (.val (.word (allocationEnd pointer (248#64))))
        {post with locals := mid.locals}).memory = mid.memory := by
      simp [setVarHOLFinite,memory]
    rw [same]
    exact watch

#print axioms actual_payload_header_strong_alloc_oh_watched

/-- **The stronger prefix through the actual `alloc 8` for `tmp`, watched.** -/
theorem actual_payload_header_strong_alloc_tmp_watched {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer extraLen : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer
      (allocationEnd (allocationEnd pointer (248#64)) (32#64)))
    (ohLocal : mid.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
    (code : state.code = originalRuntimeCode)
    (watch : WatchWord mid (pl + (24#64)) extraLen)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 7)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") = some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64)))) ∧
        WatchWord post (pl + (24#64)) extraLen) 2 (actualPayloadHeaderAt 8) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_alloc_tmp]
  refine actual_payload_header_alloc_step mid (ofString "tmp") (8#64)
    (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (actualPayloadHeaderAt 8) _
    baseFacts.2.2.2.1 (by rw [baseFacts.2.2.2.2.2]; exact code) budget ?_
  intro post memory domain postCode globals
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_,?_,?_⟩
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
  · exact HeapGlobalsFrame.alloc state mid frame (allocationEnd (allocationEnd pointer (248#64)) (32#64))
      (8#64) post globals
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ohLocal]
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · show (setVarHOLFinite (ofString "tmp") (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))
      {post with locals := mid.locals}).memory (pl + (24#64)) = HolWordLab.word extraLen
    have same : (setVarHOLFinite (ofString "tmp") (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))
        {post with locals := mid.locals}).memory = mid.memory := by
      simp [setVarHOLFinite,memory]
    rw [same]
    exact watch

#print axioms actual_payload_header_strong_alloc_tmp_watched

/-- The natural value of the header's extra-length cell. -/
theorem actual_payload_header_cell_136_nat (pointer : BitVec 64) (cap : pointer.toNat ≤ 33806089496) :
    (pointer + (136#64)).toNat = pointer.toNat + 136 := by
  have oneThirtySix : (136#64).toNat = 136 := by decide
  rw [BitVec.toNat_add_of_lt (by rw [oneThirtySix]; have := pointer.isLt; omega),oneThirtySix]

#print axioms actual_payload_header_cell_136_nat

/-- A header cell above the watched cell is a different word cell. -/
theorem actual_payload_header_cell_136_below (pointer base : BitVec 64) (offset : Nat)
    (cap : pointer.toNat ≤ 33806089496) (above : pointer.toNat + 248 ≤ base.toNat)
    (baseCap : base.toNat ≤ 33806089496) (bound : offset < 248) :
    pointer + (136#64) ≠ base + BitVec.ofNat 64 offset := by
  intro same
  have levels := congrArg BitVec.toNat same
  rw [actual_payload_header_cell_136_nat pointer cap] at levels
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bound (by norm_num))
  have sumBound : base.toNat + offset < 2^64 := by omega
  have right : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; exact sumBound),offsetNat]
  rw [right] at levels
  omega

#print axioms actual_payload_header_cell_136_below

/-- A byte cell of an address at or above an aligned base is at or above that base. -/
theorem panByteAlignHOL_toNat_ge_aligned (base : BitVec 64) (offset : Nat)
    (aligned : base.toNat % 8 = 0) (baseCap : base.toNat ≤ 33806089496)
    (bound : offset < 248) :
    base.toNat ≤ (panByteAlignHOL (base + BitVec.ofNat 64 offset)).toNat := by
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bound (by norm_num))
  have sumBound : base.toNat + offset < 2^64 := by omega
  have address : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; exact sumBound),offsetNat]
  rw [panByteAlign_toNat64,address]
  have self : base.toNat = base.toNat / 8 * 8 := by omega
  calc base.toNat = base.toNat / 8 * 8 := self
    _ ≤ (base.toNat + offset) / 8 * 8 :=
      Nat.mul_le_mul_right 8 (Nat.div_le_div_right (by omega))

#print axioms panByteAlignHOL_toNat_ge_aligned

/-- A header cell above the watched cell is a different byte cell. -/
theorem actual_payload_header_cell_136_below_byte (pointer base : BitVec 64) (offset : Nat)
    (cap : pointer.toNat ≤ 33806089496) (above : pointer.toNat + 248 ≤ base.toNat)
    (aligned : base.toNat % 8 = 0) (baseCap : base.toNat ≤ 33806089496)
    (bound : offset < 248) :
    pointer + (136#64) ≠ panByteAlignHOL (base + BitVec.ofNat 64 offset) := by
  intro same
  have levels := congrArg BitVec.toNat same
  rw [actual_payload_header_cell_136_nat pointer cap] at levels
  have base_le := panByteAlignHOL_toNat_ge_aligned base offset aligned baseCap bound
  omega

#print axioms actual_payload_header_cell_136_below_byte

/-- **The actual byte store of the test byte leaves the watched cells alone.**  The store targets the
`tmp` allocation, which is above the header, so the extra-length cell and the operand locals are
untouched. -/
theorem actual_payload_header_strong_store_byte_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer tmp extraLen : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer
      (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)))
    (ohLocal : mid.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
    (tmpLocal : mid.locals.lookup (ofString "tmp") = some (.val (.word tmp)))
    (tmpAbove : pointer.toNat ≤ tmp.toNat) (tmpAligned : tmp.toNat % 8 = 0)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (watch : WatchWord mid (pl + (24#64)) extraLen) :
    Reaches mid (actualPayloadHeaderAt 8)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
        WatchWord post (pl + (24#64)) extraLen) 0 (actualPayloadHeaderAt 9) := by
  obtain ⟨baseFacts, frame⟩ := facts
  have cellBelow := actual_payload_header_pl_cell_below pl pointer below cap
  have separate : pl + (24#64) ≠ panByteAlignHOL tmp := by
    rw [panByteAlign_eq_self_aligned tmp tmpAligned]
    intro same
    have levels := congrArg BitVec.toNat same
    have left : (pl + (24#64)).toNat = pl.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by have := pl.isLt; omega),show (24#64).toNat = 24 from by decide]
    rw [left] at levels
    omega
  rw [source_actual_payload_header_store_byte]
  refine reaches_seq mid (.storeByte (.var .local (ofString "tmp")) (.const (192#64)))
    (actualPayloadHeaderAt 9) 0 _ ?_
  have control := evaluate_storeByte_control_frame mid (.var .local (ofString "tmp")) (.const (192#64))
  cases run : evaluateHOLFiniteState mid (.storeByte (.var .local (ofString "tmp")) (.const (192#64))) with
    | mk result next =>
    rw [run] at control
    dsimp only at control ⊢
    obtain ⟨ctrl,clock,locals,globals,code,domain,_⟩ := control
    rcases ctrl with rfl | rfl
    · refine Or.inl ⟨next,⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_,?_,?_⟩,by omega,by omega,rfl⟩
      · rw [locals]; exact baseFacts.1
      · rw [locals]; exact baseFacts.2.1
      · rw [locals]; exact baseFacts.2.2.1
      · rw [globals]; exact baseFacts.2.2.2.1
      · rw [domain]; exact baseFacts.2.2.2.2.1
      · rw [code]; exact baseFacts.2.2.2.2.2
      · intro name different
        rw [globals]
        exact frame name different
      · rw [locals]; exact ohLocal
      · rw [locals]; exact tmpLocal
      · show WatchWord next (pl + (24#64)) extraLen
        have kept := evaluate_storeByte_memory_frame mid (.var .local (ofString "tmp")) (.const (192#64))
          tmp (pl + (24#64))
          (actual_payload_header_eval_local mid (ofString "tmp") tmp tmpLocal) separate
        rw [run] at kept
        unfold WatchWord at watch ⊢
        rw [kept]
        exact watch
    · refine Or.inr ⟨.error,rfl,by simp,by dsimp only; omega,by dsimp only; omega,by simp⟩

#print axioms actual_payload_header_strong_store_byte_watched

/-- **An actual allocation preserves the watched word.**  The allocator rewrites only the heap
frontier global and introduces its result local, so memory is untouched. -/
theorem actual_payload_header_alloc_next_watched {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap watched cell : BitVec 64) (name : MlS) (size : BitVec 64)
    (continuation : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (namePl : ofString "pl" ≠ name) (nameRaw : ofString "raw" ≠ name) (nameH : ofString "h" ≠ name)
    (watch : WatchWord mid watched cell)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (.decCall name .one (ofString "alloc") [(.const size)] continuation)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd heap size) ∧
        post.locals.lookup name = some (.val (.word heap)) ∧
        WatchWord post watched cell) 2 continuation := by
  refine actual_payload_header_alloc_step mid name size heap continuation _ facts.2.2.2.1
    (by rw [facts.2.2.2.2.2]; exact code) (by omega) ?_
  intro post memory domain postCode globals
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
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
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · show (setVarHOLFinite name (.val (.word heap)) {post with locals := mid.locals}).memory watched =
      HolWordLab.word cell
    have same : (setVarHOLFinite name (.val (.word heap)) {post with locals := mid.locals}).memory =
        mid.memory := by
      simp [setVarHOLFinite,memory]
    rw [same]
    exact watch

#print axioms actual_payload_header_alloc_next_watched

/-- **The actual `memzero(z8, 8)` leaves the header's extra-length cell alone.**  The zeroed scratch
interval starts above the header, so the real call preserves the watched cell and the scratch
binding. -/
theorem actual_payload_header_memzero_z8_watched {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap z8 extraLen : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (z8Local : mid.locals.lookup (ofString "z8") = some (.val (.word z8)))
    (code : state.code = originalRuntimeCode)
    (small : z8.toNat + 8 ≤ 33806089496) (aligned : z8.toNat % 8 = 0)
    (above : pointer.toNat + 248 ≤ z8.toNat) (cap : pointer.toNat ≤ 33806089496)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (watch : WatchWord mid (pointer + (136#64)) extraLen)
    (budget : 9 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 26)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        post.locals.lookup (ofString "z8") = some (.val (.word z8)) ∧
        WatchWord post (pointer + (136#64)) extraLen) 9 (actualPayloadHeaderAt 27) := by
  rw [source_actual_payload_header_memzero_z8]
  obtain ⟨window,bytes⟩ := actual_payload_header_window_domain state z8 8 fullDomain (by omega)
  have sizeNat : (8#64).toNat = 8 := by decide
  have arguments : evalListHOLFinite mid (h := fun address => Classical.propDecidable (mid.memaddrs address))
      [.var .local (ofString "z8"), .const (8#64)] =
      (some [ValueHOL.val (HolWordLab.word z8), ValueHOL.val (HolWordLab.word (8#64))] :
        Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,z8Local]
  have codeMid : mid.code = originalRuntimeCode := by
    rw [facts.2.2.2.2.2]; exact code
  obtain ⟨post, run, _, spent, kept, globals, postCode, domain, _, locals, _⟩ :=
    evaluate_memzero_aligned_call mid (.var .local (ofString "z8")) (.const (8#64)) z8 (8#64) arguments
      codeMid (by omega) (by omega) aligned
      (fun offset below => by rw [facts.2.2.2.2.1]; exact window offset (by omega))
      (fun offset below => by rw [facts.2.2.2.2.1]; exact bytes offset (by omega))
  have watched : WatchWord post (pointer + (136#64)) extraLen :=
    WatchWord.memzero mid post (.var .local (ofString "z8")) (.const (8#64)) z8 (8#64)
      (pointer + (136#64)) extraLen arguments codeMid (by omega) (by omega) aligned
      (fun offset below => by rw [facts.2.2.2.2.1]; exact window offset (by omega))
      (fun offset below => actual_payload_header_cell_136_below pointer z8 offset cap above (by omega)
        (by omega))
      (fun offset below => actual_payload_header_cell_136_below_byte pointer z8 offset cap above aligned
        (by omega) (by omega))
      (fun offset below => by rw [facts.2.2.2.2.1]; exact bytes offset (by omega))
      watch run
  refine reaches_seq mid (.call (some (none,none)) (ofString "memzero")
    [.var .local (ofString "z8"), .const (8#64)]) (actualPayloadHeaderAt 27) 9 _ ?_
  refine Or.inl ⟨post,⟨?_,?_,watched⟩,by omega,by omega,run⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [locals] using facts.1
    · simpa [locals] using facts.2.1
    · simpa [locals] using facts.2.2.1
    · simpa [globals] using facts.2.2.2.1
    · simpa [domain] using facts.2.2.2.2.1
    · simpa [postCode] using facts.2.2.2.2.2
  · simpa [locals] using z8Local

#print axioms actual_payload_header_memzero_z8_watched

/-- The watched header cell is distinct from every header cell below it. -/
theorem actual_payload_header_cell_136_offset_ne (pointer : BitVec 64) (k : Nat)
    (cap : pointer.toNat ≤ 33806089496) (bound : k < 136) :
    pointer + (136#64) ≠ pointer + BitVec.ofNat 64 k := by
  intro same
  have levels := congrArg BitVec.toNat same
  rw [actual_payload_header_cell_136_nat pointer cap] at levels
  have offsetNat : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have right : (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
  rw [right] at levels
  omega

#print axioms actual_payload_header_cell_136_offset_ne

/-- One actual store step of the header construction, keeping the typed `oh` and `tmp` locals and
the watched cell. -/
theorem actual_payload_header_store_stage_commit_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp watched cell address stored : BitVec 64) (destination value : ExpHOL 64)
    (tail : ProgHOL 64)
    (facts : ActualPayloadHeaderCommit state mid pl raw pointer heap oh tmp)
    (hDestination : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) destination = some (.val (.word address)))
    (hValue : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) value = some (.val (.word stored)))
    (domain : mid.memaddrs address)
    (separate : watched ≠ address) (watch : WatchWord mid watched cell) :
    Reaches mid (.seq (.store destination value) tail)
      (fun post => ActualPayloadHeaderCommit state post pl raw pointer heap oh tmp ∧
        WatchWord post watched cell) 0 tail := by
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  refine Or.inl ⟨sourceWriteWord mid address stored,⟨ActualPayloadHeaderCommit.write facts,?_⟩,
    by simp [sourceWriteWord],by simp [sourceWriteWord],?_⟩
  · exact WatchWord.sourceWriteWord_frame mid address stored watched cell separate watch
  · exact actual_payload_header_store_any mid destination value address stored hDestination hValue domain

#print axioms actual_payload_header_store_stage_commit_watched

/-- **The three actual stores after the keccak return and the actual `txr` allocation.**  They keep
the watched header cell, since it lies below every one of their destinations. -/
theorem actual_payload_header_after_keccak_earned_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap oh tmp extraLen : BitVec 64)
    (facts : ActualPayloadHeaderCommit state mid pl raw pointer heap oh tmp)
    (code : state.code = originalRuntimeCode)
    (wordDomain : ∀ offset : Nat, offset < 33 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (cap : pointer.toNat ≤ 33806089496)
    (watch : WatchWord mid (pointer + (136#64)) extraLen)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 10)
      (fun post => ActualPayloadHeaderCommit state post pl raw pointer (allocationEnd heap (32#64)) oh tmp ∧
        post.locals.lookup (ofString "txr") = some (.val (.word heap)) ∧
        (allocationEnd heap (32#64)).toNat ≤ 33806089496 ∧
        WatchWord post (pointer + (136#64)) extraLen) 2 (actualPayloadHeaderAt 14) := by
  have storeOh (E : PanSemStateFiniteExact 64 F)
      (pE : ActualPayloadHeaderCommit state E pl raw pointer heap oh tmp ∧
        WatchWord E (pointer + (136#64)) extraLen) :
      Reaches E (actualPayloadHeaderAt 10)
        (fun post => ActualPayloadHeaderCommit state post pl raw pointer heap oh tmp ∧
          WatchWord post (pointer + (136#64)) extraLen) 0 (actualPayloadHeaderAt 11) := by
    obtain ⟨pC,kept⟩ := pE
    rw [source_actual_payload_header_store_oh]
    exact actual_payload_header_store_stage_commit_watched state E pl raw pointer heap oh tmp
      (pointer + (136#64)) extraLen (pointer + (16#64)) oh
      (.op .add [.var .local (ofString "h"), .const (16#64)]) (.var .local (ofString "oh"))
      (actualPayloadHeaderAt 11) pC
      (actual_payload_header_eval_word_add E (ofString "h") pointer (16#64) pC.1.2.2.1)
      (actual_payload_header_eval_local E (ofString "oh") oh pC.2.1)
      (by rw [pC.1.2.2.2.2.1]; exact wordDomain 16 (by omega))
      (actual_payload_header_cell_136_offset_ne pointer 16 cap (by omega)) kept
  have store32 (E : PanSemStateFiniteExact 64 F)
      (pE : ActualPayloadHeaderCommit state E pl raw pointer heap oh tmp ∧
        WatchWord E (pointer + (136#64)) extraLen) :
      Reaches E (actualPayloadHeaderAt 11)
        (fun post => ActualPayloadHeaderCommit state post pl raw pointer heap oh tmp ∧
          WatchWord post (pointer + (136#64)) extraLen) 0 (actualPayloadHeaderAt 12) := by
    obtain ⟨pC,kept⟩ := pE
    rw [source_actual_payload_header_store_32]
    exact actual_payload_header_store_stage_commit_watched state E pl raw pointer heap oh tmp
      (pointer + (136#64)) extraLen (pointer + (24#64)) (raw + (32#64))
      (.op .add [.var .local (ofString "h"), .const (24#64)])
      (.op .add [.var .local (ofString "raw"), .const (32#64)]) (actualPayloadHeaderAt 12) pC
      (actual_payload_header_eval_word_add E (ofString "h") pointer (24#64) pC.1.2.2.1)
      (actual_payload_header_eval_word_add E (ofString "raw") raw (32#64) pC.1.2.1)
      (by rw [pC.1.2.2.2.2.1]; exact wordDomain 24 (by omega))
      (actual_payload_header_cell_136_offset_ne pointer 24 cap (by omega)) kept
  have store52 (E : PanSemStateFiniteExact 64 F)
      (pE : ActualPayloadHeaderCommit state E pl raw pointer heap oh tmp ∧
        WatchWord E (pointer + (136#64)) extraLen) :
      Reaches E (actualPayloadHeaderAt 12)
        (fun post => ActualPayloadHeaderCommit state post pl raw pointer heap oh tmp ∧
          WatchWord post (pointer + (136#64)) extraLen) 0 (actualPayloadHeaderAt 13) := by
    obtain ⟨pC,kept⟩ := pE
    rw [source_actual_payload_header_store_52]
    exact actual_payload_header_store_stage_commit_watched state E pl raw pointer heap oh tmp
      (pointer + (136#64)) extraLen (pointer + (32#64)) (raw + (52#64))
      (.op .add [.var .local (ofString "h"), .const (32#64)])
      (.op .add [.var .local (ofString "raw"), .const (52#64)]) (actualPayloadHeaderAt 13) pC
      (actual_payload_header_eval_word_add E (ofString "h") pointer (32#64) pC.1.2.2.1)
      (actual_payload_header_eval_word_add E (ofString "raw") raw (52#64) pC.1.2.1)
      (by rw [pC.1.2.2.2.2.1]; exact wordDomain 32 (by omega))
      (actual_payload_header_cell_136_offset_ne pointer 32 cap (by omega)) kept
  have stores : Reaches mid (actualPayloadHeaderAt 10)
      (fun post => ActualPayloadHeaderCommit state post pl raw pointer heap oh tmp ∧
        WatchWord post (pointer + (136#64)) extraLen) 0 (actualPayloadHeaderAt 13) :=
    reaches_trans mid (actualPayloadHeaderAt 10) (actualPayloadHeaderAt 11) (actualPayloadHeaderAt 13)
      _ _ 0 0 (storeOh mid ⟨facts,watch⟩) (fun E pE =>
        reaches_trans E (actualPayloadHeaderAt 11) (actualPayloadHeaderAt 12) (actualPayloadHeaderAt 13)
          _ _ 0 0 (store32 E pE) (fun F pF => store52 F pF))
  have allocation : ∀ E : PanSemStateFiniteExact 64 F,
      (ActualPayloadHeaderCommit state E pl raw pointer heap oh tmp ∧
        WatchWord E (pointer + (136#64)) extraLen) → 2 ≤ E.clock →
      Reaches E (actualPayloadHeaderAt 13)
        (fun post => ActualPayloadHeaderCommit state post pl raw pointer (allocationEnd heap (32#64)) oh tmp ∧
          post.locals.lookup (ofString "txr") = some (.val (.word heap)) ∧
          (allocationEnd heap (32#64)).toNat ≤ 33806089496 ∧
          WatchWord post (pointer + (136#64)) extraLen) 2 (actualPayloadHeaderAt 14) := by
    intro E pE clockBound
    obtain ⟨pC,kept⟩ := pE
    rw [source_actual_payload_header_alloc_txr]
    refine actual_payload_header_alloc_step_earned E (ofString "txr") (32#64) heap
      (actualPayloadHeaderAt 14) _ pC.1.2.2.2.1 (by rw [pC.1.2.2.2.2.2]; exact code)
      clockBound ?_
    intro post memory domain postCode globals floor
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩,?_,floor,?_⟩
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pC.1.1]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pC.1.2.1]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pC.1.2.2.1]
    · simp only [setVarHOLFinite]
      rw [globals]
      simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp only [setVarHOLFinite]
      rw [domain]
      exact pC.1.2.2.2.2.1
    · simp only [setVarHOLFinite]
      rw [postCode]
      exact pC.1.2.2.2.2.2
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pC.2.1]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pC.2.2]
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · show (setVarHOLFinite (ofString "txr") (.val (.word heap))
        {post with locals := E.locals}).memory (pointer + (136#64)) = HolWordLab.word extraLen
      have same : (setVarHOLFinite (ofString "txr") (.val (.word heap))
          {post with locals := E.locals}).memory = E.memory := by
        simp [setVarHOLFinite,memory]
      rw [same]
      exact kept
  rcases stores with ⟨E, pE, c1, c2, sc⟩ | ab
  · rcases allocation E pE (by omega) with ⟨post, pP, a1, a2, asc⟩ | ab2
    · exact Or.inl ⟨post, pP, by omega, by omega, scoped_trans sc asc⟩
    · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans i1, i2, by omega, by omega, fun k => i5 (by omega)⟩
  · exact Or.inr (stAbort_mono mid _ 0 2 (by omega) ab)

#print axioms actual_payload_header_after_keccak_earned_watched

/-- **The watched prefix from statement 0 to statement 9.**  The actual loads, the header allocation,
the actual `memzero(h, 248)`, both header stores, the `oh` and `tmp` allocations and the actual byte
store run in 255 ticks, or abort, and the loader's extra-length cell is untouched throughout. -/
theorem actual_payload_header_strong_prefix_0_to_9_watched {F : Type}
    (state : PanSemStateFiniteExact 64 F) (si pl raw pointer extraLen : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (below : pl.toNat + 136 ≤ pointer.toNat)
    (watch : WatchWord state (pl + (24#64)) extraLen)
    (budget : 255 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") =
          some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64)))) ∧
        WatchWord post (pl + (24#64)) extraLen) 255 (actualPayloadHeaderAt 9) := by
  rcases actual_payload_header_strong_prefix_watched state si pl raw pointer extraLen siLocal
    siDomain siCell plDomain plCell code heapGlobal pointerBound watch (by omega) with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · rcases actual_payload_header_memzero_watched state E pl raw pointer extraLen pE.1 code
      pE.2.1 aligned pointerBound wordDomain byteDomain below pE.2.2 (by omega) with
      ⟨G, pG, d1, d2, sd⟩ | ab2
    · rcases actual_payload_header_strong_stores_watched state G pl raw pointer extraLen pG.1 below
        pointerBound pG.2.2 with ⟨I, pI, e1, e2, se⟩ | ab3
      · rcases actual_payload_header_strong_alloc_oh_watched state I pl raw pointer extraLen pI.1 code
          pI.2 (by omega) with ⟨K, pK, f1, f2, sf⟩ | ab4
        · rcases actual_payload_header_strong_alloc_tmp_watched state K pl raw pointer extraLen pK.1
            pK.2.1 code pK.2.2.1 (by omega) with ⟨M, pM, g1, g2, sg⟩ | ab5
          · rcases actual_payload_header_strong_store_byte_watched state M pl raw pointer
              (allocationEnd (allocationEnd pointer (248#64)) (32#64)) extraLen pM.1 pM.2.1 pM.2.2.1
              (by
                have h248 : (248#64).toNat = 248 := by decide
                have h32 : (32#64).toNat = 32 := by decide
                have baseHigh : (allocationEnd pointer (248#64)).toNat ≤ pointer.toNat + 255 := by
                  rw [allocationEnd_toNat pointer (248#64) (by omega)]
                  have := Nat.div_mul_le_self (pointer.toNat + 248 + 7) 8
                  omega
                have base := allocationEnd_covers_noWrap pointer (248#64)
                  (by have := pointer.isLt; omega)
                have top := allocationEnd_covers_noWrap (allocationEnd pointer (248#64)) (32#64)
                  (by have := (allocationEnd pointer (248#64)).isLt; omega)
                omega)
              (allocationEnd_aligned (allocationEnd pointer (248#64)) (32#64)) below pointerBound
              pM.2.2.2 with ⟨J, pJ, h1, h2, sh⟩ | ab6
            · refine Or.inl ⟨J, pJ, by omega, by omega,
                scoped_trans sc (scoped_trans sd (scoped_trans se (scoped_trans sf (scoped_trans sg sh))))⟩
            · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab6
              have ck := (scoped_trans sc (scoped_trans sd (scoped_trans se (scoped_trans sf sg)))).2.1
              exact Or.inr ⟨x, (scoped_trans sc (scoped_trans sd (scoped_trans se
                (scoped_trans sf sg)))).1.trans i1, i2, by omega, by omega, fun k => i5 (by omega)⟩
          · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab5
            have ck := (scoped_trans sc (scoped_trans sd (scoped_trans se sf))).2.1
            exact Or.inr ⟨x, (scoped_trans sc (scoped_trans sd (scoped_trans se sf))).1.trans i1, i2,
              by omega, by omega, fun k => i5 (by omega)⟩
        · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab4
          have ck := (scoped_trans sc (scoped_trans sd se)).2.1
          exact Or.inr ⟨x, (scoped_trans sc (scoped_trans sd se)).1.trans i1, i2, by omega, by omega,
            fun k => i5 (by omega)⟩
      · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab3
        have ck := (scoped_trans sc sd).2.1
        exact Or.inr ⟨x, (scoped_trans sc sd).1.trans i1, i2, by omega, by omega,
          fun k => i5 (by omega)⟩
    · obtain ⟨x, i1, i2, i3, i4, i5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans i1, i2, by omega, by omega, fun k => i5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 2 255 (by omega) ab)

#print axioms actual_payload_header_strong_prefix_0_to_9_watched

/-- The word size used by the exact store loop. -/
theorem panBytesInWord64 : panBytesInWord 64 = (8#64) := by decide

#print axioms panBytesInWord64

/-- **A multi-cell store leaves every cell it does not write alone.**  The store loop writes the
addresses `address`, `address + 8`, ... for as many words as the payload flattens to, so a watched
cell distinct from all of them survives a successful store. -/
theorem panMemStoresHOL_frame (address watched : BitVec 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (memory : BitVec 64 → HolWordLab 64) :
    ∀ (words : List (HolWordLab 64)),
      (∀ index, index < words.length → watched ≠ address + BitVec.ofNat 64 (8 * index)) →
      ∀ updated, panMemStoresHOL address words domain memory = some updated →
        updated watched = memory watched := by
  intro words
  induction words generalizing address memory with
  | nil =>
    intro separate updated run
    simp only [panMemStoresHOL, Option.some.injEq] at run
    rw [← run]
  | cons value rest induction =>
    intro separate updated run
    simp only [panMemStoresHOL] at run
    split at run
    · rename_i storedValue store
      have stored : storedValue watched = memory watched := by
        rw [panMemStoreHOL] at store
        split at store
        · simp only [Option.some.injEq] at store
          rw [← store]
          have different : watched ≠ address := by
            have := separate 0 (by simp)
            simpa using this
          simp [different]
        · exact absurd store (by simp)
      refine (induction (address + panBytesInWord 64) storedValue ?_ updated run).trans stored
      intro index bound
      have shifted : address + panBytesInWord 64 + BitVec.ofNat 64 (8 * index) =
          address + BitVec.ofNat 64 (8 * (index + 1)) := by
        rw [panBytesInWord64]
        bv_omega
      rw [shifted]
      exact separate (index + 1) (by simpa using bound)
    · exact absurd run (by simp)

#print axioms panMemStoresHOL_frame
#print axioms panMemStoresHOL_frame

/-- **A store of a flattened payload changes only the cells it writes.** -/
theorem evaluate_store_flat_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address watched : BitVec 64) (payload : ValueHOL 64)
    (words : List (HolWordLab 64))
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value = some payload)
    (flat : flattenHOL payload = words)
    (untouched : ∀ index, index < words.length → watched ≠ address + BitVec.ofNat 64 (8 * index)) :
    (evaluateHOLFiniteState state (.store destination value)).2.memory watched =
      state.memory watched := by
  rw [evaluateHOLFiniteState_store,addressEval,valueEval]
  dsimp only
  rw [flat]
  classical
  cases run : panMemStoresHOL address words state.memaddrs state.memory with
  | none => rfl
  | some updated =>
    exact panMemStoresHOL_frame address watched state.memaddrs state.memory words untouched updated run

#print axioms evaluate_store_flat_memory_frame

/-- One actual header store, keeping the construction facts and a watched cell below the store. -/
theorem actual_payload_header_store_step_prefix_watched_flat {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (payload : ValueHOL 64) (words : List (HolWordLab 64))
    (shape : actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (destShape : destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (valueEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) value = some payload)
    (flat : flattenHOL payload = words)
    (untouched : ∀ offset, offset < words.length →
      watched ≠ pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset))
    (watch : WatchWord mid watched cell) :
    Reaches mid (actualPayloadHeaderAt index)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        WatchWord post watched cell) 0 tail := by
  have addressEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) destination =
      some (.val (.word (pointer + BitVec.ofNat 64 k))) := by
    rw [destShape]
    exact actual_payload_header_eval_word_add mid (ofString "h") pointer (BitVec.ofNat 64 k)
      facts.2.2.1
  rw [shape]
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · have frameMemory : memory watched = mid.memory watched := by
      have runMemory : (evaluateHOLFiniteState mid (.store destination value)).2.memory watched =
          mid.memory watched :=
        evaluate_store_flat_memory_frame mid destination value (pointer + BitVec.ofNat 64 k) watched
          payload words addressEval valueEval flat untouched
      rw [run] at runMemory
      exact runMemory
    refine Or.inl ⟨{mid with memory := memory},⟨?_prefix,?_watch⟩,by simp,by simp,run⟩
    · refine ⟨?_,?_,?_,?_,?_,?_⟩
      · simpa using facts.1
      · simpa using facts.2.1
      · simpa using facts.2.2.1
      · simpa using facts.2.2.2.1
      · exact facts.2.2.2.2.1
      · exact facts.2.2.2.2.2
    · show memory watched = HolWordLab.word cell
      rw [frameMemory]
      exact watch

#print axioms actual_payload_header_store_step_prefix_watched_flat

/-- The loader's extra-length cell is below every header store cell. -/
theorem actual_payload_header_pl_cell_flat_separate (pl pointer : BitVec 64) (k offset : Nat)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (bound : 8 * offset < 248) (kBound : k < 248) :
    pl + (24#64) ≠ pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset) := by
  intro same
  have levels := congrArg BitVec.toNat same
  have cellNat : (pl + (24#64)).toNat = pl.toNat + 24 := by
    have h24 : (24#64).toNat = 24 := by decide
    rw [BitVec.toNat_add_of_lt (by rw [h24]; have := pl.isLt; omega),h24]
  have step : ∀ n : Nat, n < 248 → (BitVec.ofNat 64 n).toNat = n := by
    intro n bound
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have inner : (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k := by
    rw [BitVec.toNat_add_of_lt (by rw [step k kBound]; omega),step k kBound]
  have outer : (pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset)).toNat =
      pointer.toNat + k + 8 * offset := by
    rw [BitVec.toNat_add_of_lt (by rw [step (8*offset) bound]; omega),step (8*offset) bound,inner]
  rw [cellNat,outer] at levels
  omega

#print axioms actual_payload_header_pl_cell_flat_separate

/-- A small constant offset of the loader pointer does not wrap and stays below the cap. -/
theorem actual_payload_header_pl_add_toNat (pl pointer : BitVec 64) (k : Nat)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (bound : k < 136) : (pl + BitVec.ofNat 64 k).toNat = pl.toNat + k := by
  have small : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [small]; omega),small]

/-- A small constant offset of the loader pointer is inside the reachable memory. -/
theorem actual_payload_header_pl_add_below (pl pointer : BitVec 64) (k : Nat)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (bound : k < 136) : (pl + BitVec.ofNat 64 k).toNat < 33806089496 := by
  rw [actual_payload_header_pl_add_toNat pl pointer k below cap bound]
  omega

/-- A small constant offset of the header pointer is inside the reachable memory. -/
theorem actual_payload_header_pointer_add_below (pointer : BitVec 64) (k : Nat)
    (room : pointer.toNat + 248 ≤ 33806089496) (bound : k < 248) :
    (pointer + BitVec.ofNat 64 k).toNat < 33806089496 := by
  have small : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have noWrap : pointer.toNat + (BitVec.ofNat 64 k).toNat < 2^64 := by rw [small]; omega
  rw [BitVec.toNat_add_of_lt noWrap,small]
  omega

#print axioms actual_payload_header_pointer_add_below

/-- **The actual header stores from statement 14 to statement 24.**  The nine header stores, then the
actual copy of the loader's extra-length cell into `h+136`; 0 ticks, or abort. -/
theorem actual_payload_header_stores_14_to_24_watched {F : Type}
    (state entry : PanSemStateFiniteExact 64 F) (pl raw pointer extraLen txr : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state entry pl raw pointer (actualPayloadHeaderTxrFloor pointer))
    (txrLocal : entry.locals.lookup (ofString "txr") = some (.val (.word txr)))
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (room : pointer.toNat + 248 ≤ 33806089496)
    (watch : WatchWord entry (pl + (24#64)) extraLen) :
    Reaches entry (actualPayloadHeaderAt 14)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
          (actualPayloadHeaderTxrFloor pointer) ∧
        post.memory (pointer + (136#64)) = .word extraLen) 0 (actualPayloadHeaderAt 24) := by
  have separation : ∀ (k offset : Nat), 8 * offset < 248 → k < 248 →
      pl + (24#64) ≠ pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset) :=
    fun k offset bound kBound =>
      actual_payload_header_pl_cell_flat_separate pl pointer k offset below cap bound kBound
  have wordStep : ∀ (start : PanSemStateFiniteExact 64 F) (index k : Nat)
      (destination value : ExpHOL 64) (tail : ProgHOL 64) (payload : ValueHOL 64)
      (words : List (HolWordLab 64)),
      ActualPayloadHeaderPrefix state start pl raw pointer (actualPayloadHeaderTxrFloor pointer) →
      WatchWord start (pl + (24#64)) extraLen →
      actualPayloadHeaderAt index = .seq (.store destination value) tail →
      destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)] →
      @evalHOLExact 64 F _ start.toExact (fun a => Classical.propDecidable (start.memaddrs a))
        value = some payload →
      flattenHOL payload = words →
      (∀ offset, offset < words.length → pl + (24#64) ≠
        pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset)) →
      Reaches start (actualPayloadHeaderAt index)
        (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
            (actualPayloadHeaderTxrFloor pointer) ∧
          WatchWord post (pl + (24#64)) extraLen) 0 tail :=
    fun start index k destination value tail payload words startFacts kept shape destShape valueEval
      flat untouched =>
      actual_payload_header_store_step_prefix_watched_flat state start pl raw pointer
        (actualPayloadHeaderTxrFloor pointer) (pl + (24#64)) extraLen index k destination value tail
        payload words shape destShape startFacts valueEval flat untouched kept
  have one : ∀ (k : Nat) (offset : Nat), offset < 1 → 8 * offset < 248 := by
    intro k offset bound
    have : offset = 0 := by omega
    subst this
    omega
  refine reaches_trans entry (actualPayloadHeaderAt 14) (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep entry 14 40 (.op .add [.var .local (ofString "h"), .const (40#64)])
      (.var .local (ofString "txr")) (actualPayloadHeaderAt 15) (.val (.word txr)) [.word txr]
      facts watch rfl rfl
      (actual_payload_header_eval_local entry (ofString "txr") txr txrLocal) (by simp [flattenHOL])
      (by intro offset bound; exact separation 40 offset (one 40 offset bound) (by omega))) ?_
  intro E1 pE1
  refine reaches_trans E1 (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E1 15 48 (.op .add [.var .local (ofString "h"), .const (48#64)])
      (.op .add [.var .local (ofString "raw"), .const (84#64)]) (actualPayloadHeaderAt 16)
      (.val (.word (raw + (84#64)))) [.word (raw + (84#64))]
      pE1.1 pE1.2 rfl rfl
      (actual_payload_header_eval_word_add E1 (ofString "raw") raw (84#64) pE1.1.2.1) (by simp [flattenHOL])
      (by intro offset bound; exact separation 48 offset (one 48 offset bound) (by omega))) ?_
  intro E2 pE2
  refine reaches_trans E2 (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E2 16 56 (.op .add [.var .local (ofString "h"), .const (56#64)])
      (.op .add [.var .local (ofString "raw"), .const (116#64)]) (actualPayloadHeaderAt 17)
      (.val (.word (raw + (116#64)))) [.word (raw + (116#64))]
      pE2.1 pE2.2 rfl rfl
      (actual_payload_header_eval_word_add E2 (ofString "raw") raw (116#64) pE2.1.2.1) (by simp [flattenHOL])
      (by intro offset bound; exact separation 56 offset (one 56 offset bound) (by omega))) ?_
  intro E3 pE3
  refine reaches_trans E3 (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E3 17 64 (.op .add [.var .local (ofString "h"), .const (64#64)])
      (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)])
      (actualPayloadHeaderAt 18)
      (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))])
      [.word (0#64),.word (0#64),.word (0#64),.word (0#64)]
      pE3.1 pE3.2 rfl rfl
      (by simp [evalHOLExact,evalListHOLExact]) (by simp [flattenHOL])
      (by
        intro offset bound
        have tiny : offset < 4 := by simpa using bound
        interval_cases offset
        · exact separation 64 0 (by omega) (by omega)
        · exact separation 64 1 (by omega) (by omega)
        · exact separation 64 2 (by omega) (by omega)
        · exact separation 64 3 (by omega) (by omega))) ?_
  intro E4 pE4
  refine reaches_trans E4 (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E4 18 96 (.op .add [.var .local (ofString "h"), .const (96#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (80#64)]))
      (actualPayloadHeaderAt 19) (.val (E4.memory (pl + (80#64)))) [E4.memory (pl + (80#64))]
      pE4.1 pE4.2 rfl rfl
      (actual_payload_header_eval_load_one E4 (ofString "pl") pl (80#64) pE4.1.1
        (by rw [pE4.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 80 below cap (by omega)))) (by simp [flattenHOL])
      (by intro offset bound; exact separation 96 offset (one 96 offset bound) (by omega))) ?_
  intro E5 pE5
  refine reaches_trans E5 (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E5 19 104 (.op .add [.var .local (ofString "h"), .const (104#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (88#64)]))
      (actualPayloadHeaderAt 20) (.val (E5.memory (pl + (88#64)))) [E5.memory (pl + (88#64))]
      pE5.1 pE5.2 rfl rfl
      (actual_payload_header_eval_load_one E5 (ofString "pl") pl (88#64) pE5.1.1
        (by rw [pE5.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 88 below cap (by omega)))) (by simp [flattenHOL])
      (by intro offset bound; exact separation 104 offset (one 104 offset bound) (by omega))) ?_
  intro E6 pE6
  refine reaches_trans E6 (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E6 20 112 (.op .add [.var .local (ofString "h"), .const (112#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (96#64)]))
      (actualPayloadHeaderAt 21) (.val (E6.memory (pl + (96#64)))) [E6.memory (pl + (96#64))]
      pE6.1 pE6.2 rfl rfl
      (actual_payload_header_eval_load_one E6 (ofString "pl") pl (96#64) pE6.1.1
        (by rw [pE6.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 96 below cap (by omega)))) (by simp [flattenHOL])
      (by intro offset bound; exact separation 112 offset (one 112 offset bound) (by omega))) ?_
  intro E7 pE7
  refine reaches_trans E7 (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E7 21 120 (.op .add [.var .local (ofString "h"), .const (120#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (104#64)]))
      (actualPayloadHeaderAt 22) (.val (E7.memory (pl + (104#64)))) [E7.memory (pl + (104#64))]
      pE7.1 pE7.2 rfl rfl
      (actual_payload_header_eval_load_one E7 (ofString "pl") pl (104#64) pE7.1.1
        (by rw [pE7.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 104 below cap (by omega)))) (by simp [flattenHOL])
      (by intro offset bound; exact separation 120 offset (one 120 offset bound) (by omega))) ?_
  intro E8 pE8
  refine reaches_trans E8 (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 23) (actualPayloadHeaderAt 24)
    _ _ 0 0
    (wordStep E8 22 128 (.op .add [.var .local (ofString "h"), .const (128#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (16#64)]))
      (actualPayloadHeaderAt 23) (.val (E8.memory (pl + (16#64)))) [E8.memory (pl + (16#64))]
      pE8.1 pE8.2 rfl rfl
      (actual_payload_header_eval_load_one E8 (ofString "pl") pl (16#64) pE8.1.1
        (by rw [pE8.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 16 below cap (by omega)))) (by simp [flattenHOL])
      (by intro offset bound; exact separation 128 offset (one 128 offset bound) (by omega))) ?_
  intro E9 pE9
  exact actual_payload_header_store_136_stage state E9 pl raw pointer
    (actualPayloadHeaderTxrFloor pointer) extraLen pE9.1
    (by rw [pE9.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pl_add_below pl pointer 24 below cap (by omega)))
    (by show E9.memory (pl + (24#64)) = HolWordLab.word extraLen; exact pE9.2)
    (by rw [pE9.1.2.2.2.2.1]; exact fullDomain _ (actual_payload_header_pointer_add_below pointer 136 room (by omega)))

#print axioms actual_payload_header_stores_14_to_24_watched


/-- **The actual struct declaration of the tail binds a four-word value.**  Beyond the frame lemma,
the declaration's shape test pins the number of cells the bound value occupies, which is what the
following four-word store needs. -/
theorem actual_payload_header_dec_four_watched {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap watched extraLen : BitVec 64) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL 64) (body : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (namePl : name ≠ ofString "pl") (nameRaw : name ≠ ofString "raw") (nameH : name ≠ ofString "h")
    (watch : WatchWord mid watched extraLen)
    (four : sizeOfShapeHOL shape = 4)
    (wf : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    Reaches mid (.dec name shape initializer body)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        WatchWord post watched extraLen ∧
        ∃ v, post.locals.lookup name = some v ∧ (flattenHOL v).length = 4) 0 body := by
  rw [Reaches, evaluateHOLFiniteState_dec_total]
  dsimp only
  cases he : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
    initializer with
  | none => exact Or.inr (stAbort_error mid 0)
  | some v =>
    by_cases ok : shapeEqHOL shape (shapeOfHOLExact v)
    · have okTrue : shapeEqHOL shape (shapeOfHOLExact v) = true := ok
      have shapeEq : shapeOfHOLExact v = shape :=
        ((shapeEqHOL_eq_true shape (shapeOfHOLExact v)).mp okTrue).symm
      have lengthFour : (flattenHOL v).length = 4 := by
        rw [flattenHOL_length_eq_sizeOfShapeHOL v (by rw [shapeEq]; exact wf),shapeEq,four]
      obtain ⟨plLocal,rawLocal,hLocal,heapGlobal,domain,code⟩ := facts
      simp only [ok,if_true] at *
      refine Or.inl ⟨setVarHOLFinite name v mid,
        ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,⟨v,?_,lengthFour⟩⟩,?_,?_,?_⟩
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namePl] using plLocal
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nameRaw] using rawLocal
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nameH] using hLocal
      · simpa only [setVarHOLFinite] using heapGlobal
      · simpa only [setVarHOLFinite] using domain
      · simpa only [setVarHOLFinite] using code
      · simpa only [WatchWord,setVarHOLFinite] using watch
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simp [setVarHOLFinite]
      · simp [setVarHOLFinite]
      · exact scoped_restore _ _
    · simp only [ok,if_false] at *
      exact Or.inr ⟨.error,rfl,by simp,by simp,by simp,by simp⟩

#print axioms actual_payload_header_dec_four_watched

/-- A one-word load yields a single-cell value. -/
theorem eval_load_one_val {F : Type} (state : PanSemStateFiniteExact 64 F) (address : ExpHOL 64)
    (value : ValueHOL 64)
    (loaded : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one address) = some value) :
    ∃ cell, value = .val cell := by
  rw [evalHOLExact] at loaded
  split at loaded
  · split at loaded
    · rename_i content contentEval
      by_cases inDomain : state.memaddrs content
      · simp only [memLoadHOLExact,inDomain,if_true] at loaded
        exact ⟨state.memory content,by simpa using loaded.symm⟩
      · simp only [memLoadHOLExact,inDomain,if_false] at loaded
        exact absurd loaded (by simp)
    · exact absurd loaded (by simp)
  · exact absurd loaded (by simp)

#print axioms eval_load_one_val

/-- **A load-valued store writes exactly one cell.**  The value expression is a one-word load, so
whatever it evaluates to occupies a single cell: a watched cell elsewhere survives, or the store
rejects. -/
theorem evaluate_store_load_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination address : ExpHOL 64) (watched current : BitVec 64)
    (destEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination =
      some (.val (.word current)))
    (separate : watched ≠ current) :
    (evaluateHOLFiniteState state (.store destination (.load .one address))).2.memory watched =
      state.memory watched := by
  rw [evaluateHOLFiniteState_store,destEval]
  dsimp only
  classical
  cases loaded : evalHOLExact state.toExact (.load .one address) with
  | none => simp [loaded]
  | some value =>
    obtain ⟨cell,shape⟩ := eval_load_one_val state address value loaded
    subst shape
    simp only [flattenHOL]
    cases run : panMemStoresHOL current [cell] state.memaddrs state.memory with
    | none => rfl
    | some updated =>
      refine panMemStoresHOL_frame current watched state.memaddrs state.memory [cell] ?_ updated run
      intro index bound
      have zero : index = 0 := by simpa using bound
      subst zero
      simpa using separate

#print axioms evaluate_store_load_memory_frame

/-- One actual header store once the store's memory frame is known. -/
theorem actual_payload_header_store_step_prefix_watched_frame {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (shape : actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (destShape : destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (frame : (evaluateHOLFiniteState mid (.store destination value)).2.memory watched =
      mid.memory watched)
    (watch : WatchWord mid watched cell) :
    Reaches mid (actualPayloadHeaderAt index)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        WatchWord post watched cell) 0 tail := by
  rw [shape]
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · have frameMemory : memory watched = mid.memory watched := by
      rw [run] at frame
      exact frame
    refine Or.inl ⟨{mid with memory := memory},⟨?_prefix,?_watch⟩,by simp,by simp,run⟩
    · refine ⟨?_,?_,?_,?_,?_,?_⟩
      · simpa using facts.1
      · simpa using facts.2.1
      · simpa using facts.2.2.1
      · simpa using facts.2.2.2.1
      · exact facts.2.2.2.2.1
      · exact facts.2.2.2.2.2
    · show memory watched = HolWordLab.word cell
      rw [frameMemory]
      exact watch

#print axioms actual_payload_header_store_step_prefix_watched_frame

/-- One actual load-valued header store, keeping the construction facts and a watched cell. -/
theorem actual_payload_header_store_step_load_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (address : ExpHOL 64) (tail : ProgHOL 64)
    (shape : actualPayloadHeaderAt index = .seq
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
        (.load .one address)) tail)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (separate : watched ≠ pointer + BitVec.ofNat 64 k)
    (watch : WatchWord mid watched cell) :
    Reaches mid (actualPayloadHeaderAt index)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        WatchWord post watched cell) 0 tail := by
  refine actual_payload_header_store_step_prefix_watched_frame state mid pl raw pointer heap
    watched cell index k (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (.load .one address) tail shape rfl facts ?_ watch
  exact evaluate_store_load_memory_frame mid (.op .add [.var .local (ofString "h"),
    .const (BitVec.ofNat 64 k)]) address watched (pointer + BitVec.ofNat 64 k)
    (actual_payload_header_eval_word_add mid (ofString "h") pointer (BitVec.ofNat 64 k) facts.2.2.1)
    separate

#print axioms actual_payload_header_store_step_load_watched

/-- Statement 28 is the actual struct declaration with the four-field word shape. -/
theorem source_actual_payload_header_dec_bf_shape :
    ∃ initializer, actualPayloadHeaderAt 28 = .dec (ofString "bf")
      (ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) initializer
      (actualPayloadHeaderAt 29) := ⟨_,rfl⟩

#print axioms source_actual_payload_header_dec_bf_shape

/-- The loader pointer's watched cell in terms of the header pointer. -/
theorem actual_payload_header_pointer_cell_separate (pointer : BitVec 64) (k : Nat)
    (kBound : k < 248) (different : 136 ≠ k) :
    pointer + (136#64) ≠ pointer + BitVec.ofNat 64 k := by
  intro same
  have cancel : (136#64) = BitVec.ofNat 64 k := by
    have step := congrArg (fun value => value - pointer) same
    simpa using step
  have levels := congrArg BitVec.toNat cancel
  have small : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [show (136#64).toNat = 136 from by decide,small] at levels
  exact different levels

#print axioms actual_payload_header_pointer_cell_separate





/-- A local holding an arbitrary value evaluates to it. -/
theorem actual_payload_header_eval_local_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64)
    (held : state.locals.lookup name = some value) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .local name) = some value := by
  simp [evalHOLExact,held]

#print axioms actual_payload_header_eval_local_value




/-- **The actual header construction tail, with the watched extra-length cell.**  Statements 24 to 39
of `payload_header`: the word stores, the actual allocations, memzero and declaration of the tail, the
loading stores, and finally the `h+240` load; 17 ticks, or abort.  The loader's extra-length cell,
already copied to `h+136`, survives the whole tail. -/
theorem actual_payload_header_construction_24_to_40_watched {F : Type}
    (state entry : PanSemStateFiniteExact 64 F) (pl raw pointer extraLen : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state entry pl raw pointer (actualPayloadHeaderTxrFloor pointer))
    (code : state.code = originalRuntimeCode)
    (watch : WatchWord entry (pointer + (136#64)) extraLen)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (h0Aligned : (actualPayloadHeaderTxrFloor pointer).toNat % 8 = 0) (h0Above : pointer.toNat + 248 ≤ (actualPayloadHeaderTxrFloor pointer).toNat)
    (h0Small : (actualPayloadHeaderTxrFloor pointer).toNat + 8 ≤ 33806089496)
    (budget : 17 ≤ entry.clock) :
    Reaches entry (actualPayloadHeaderAt 24) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 17 (actualPayloadHeaderAt 40) := by
  obtain ⟨bfInitializer, decSpine⟩ := source_actual_payload_header_dec_bf_shape
  have storeWord : ∀ (start : PanSemStateFiniteExact 64 F) (heap : BitVec 64) (index k : Nat)
      (destination value : ExpHOL 64) (tail : ProgHOL 64) (payload : ValueHOL 64)
      (words : List (HolWordLab 64)),
      ActualPayloadHeaderPrefix state start pl raw pointer heap →
      WatchWord start (pointer + (136#64)) extraLen →
      actualPayloadHeaderAt index = .seq (.store destination value) tail →
      destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)] →
      @evalHOLExact 64 F _ start.toExact (fun a => Classical.propDecidable (start.memaddrs a))
        value = some payload →
      flattenHOL payload = words →
      (∀ offset, offset < words.length → (pointer + (136#64)) ≠
        pointer + BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * offset)) →
      Reaches start (actualPayloadHeaderAt index)
        (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
          WatchWord post (pointer + (136#64)) extraLen) 0 tail :=
    fun start heap index k destination value tail payload words startFacts kept shape destShape
      valueEval flat untouched =>
      actual_payload_header_store_step_prefix_watched_flat state start pl raw pointer heap
        (pointer + (136#64)) extraLen index k destination value tail payload words shape destShape startFacts
        valueEval flat untouched kept
  have storeLoad : ∀ (start : PanSemStateFiniteExact 64 F) (heap : BitVec 64) (index k : Nat)
      (address : ExpHOL 64) (tail : ProgHOL 64),
      ActualPayloadHeaderPrefix state start pl raw pointer heap →
      WatchWord start (pointer + (136#64)) extraLen →
      actualPayloadHeaderAt index = .seq (.store (.op .add [.var .local (ofString "h"),
        .const (BitVec.ofNat 64 k)]) (.load .one address)) tail →
      (pointer + (136#64)) ≠ pointer + BitVec.ofNat 64 k →
      Reaches start (actualPayloadHeaderAt index)
        (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
          WatchWord post (pointer + (136#64)) extraLen) 0 tail :=
    fun start heap index k address tail startFacts kept shape separate =>
      actual_payload_header_store_step_load_watched state start pl raw pointer heap (pointer + (136#64)) extraLen
        index k address tail shape startFacts separate kept
  have single : ∀ (offset : Nat), offset < 1 → offset = 0 := by
    intro offset bound
    omega

  refine reaches_trans_budget entry (actualPayloadHeaderAt 24) (actualPayloadHeaderAt 25) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (actualPayloadHeaderTxrFloor pointer) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 17 ?_ (storeWord entry (actualPayloadHeaderTxrFloor pointer) 24 144
      (.op .add [.var .local (ofString "h"), .const (144#64)]) (.op .add [.var .local (ofString "raw"), .const (372#64)])
      (actualPayloadHeaderAt 25) (.val (.word (raw + (372#64)))) [HolWordLab.word (raw + (372#64))] facts watch rfl rfl
      (actual_payload_header_eval_word_add entry (ofString "raw") raw (372#64) facts.2.1) (by simp [flattenHOL]) (by intro offset bound; have zero := single offset bound; subst zero; simpa using actual_payload_header_pointer_cell_separate pointer 144 (by omega) (by omega))) ?_
  · omega
  intro n1 p1 h1
  refine reaches_trans_budget n1 (actualPayloadHeaderAt 25) (actualPayloadHeaderAt 26) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) ∧
        post.locals.lookup (ofString "z8") = some (.val (.word (actualPayloadHeaderTxrFloor pointer))) ∧
        WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 2 15 ?_ (actual_payload_header_alloc_next_watched state n1 pl raw pointer (actualPayloadHeaderTxrFloor pointer) (pointer + (136#64)) extraLen (ofString "z8") (8#64) (actualPayloadHeaderAt 26) p1.1 code (by decide) (by decide) (by decide) p1.2 (by omega)) ?_
  · omega
  intro n2 p2 h2
  refine reaches_trans_budget n2 (actualPayloadHeaderAt 26) (actualPayloadHeaderAt 27) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) ∧
        post.locals.lookup (ofString "z8") = some (.val (.word (actualPayloadHeaderTxrFloor pointer))) ∧
        WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 9 6 ?_ (actual_payload_header_memzero_z8_watched state n2 pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (actualPayloadHeaderTxrFloor pointer) extraLen p2.1 p2.2.1 code h0Small h0Aligned h0Above cap fullDomain p2.2.2 (by omega)) ?_
  · omega
  intro n3 p3 h3
  refine reaches_trans_budget n3 (actualPayloadHeaderAt 27) (actualPayloadHeaderAt 28) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 6 ?_ (storeWord n3 (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) 27 152
      (.op .add [.var .local (ofString "h"), .const (152#64)]) (.var .local (ofString "z8"))
      (actualPayloadHeaderAt 28) (.val (.word (actualPayloadHeaderTxrFloor pointer))) [HolWordLab.word (actualPayloadHeaderTxrFloor pointer)] p3.1 p3.2.2 rfl rfl
      (actual_payload_header_eval_local n3 (ofString "z8") (actualPayloadHeaderTxrFloor pointer) p3.2.1) (by simp [flattenHOL]) (by intro offset bound; have zero := single offset bound; subst zero; simpa using actual_payload_header_pointer_cell_separate pointer 152 (by omega) (by omega))) ?_
  · omega
  intro n4 p4 h4
  refine reaches_trans_budget n4 (actualPayloadHeaderAt 28) (actualPayloadHeaderAt 29) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) ∧
        WatchWord post (pointer + (136#64)) extraLen ∧
        ∃ value, post.locals.lookup (ofString "bf") = some value ∧
          (flattenHOL value).length = 4) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 6 ?_ (by
      rw [decSpine]
      exact actual_payload_header_dec_four_watched state n4 pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (pointer + (136#64)) extraLen (ofString "bf") (ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) bfInitializer (actualPayloadHeaderAt 29) p4.1 (by decide) (by decide) (by decide) p4.2 (by decide) (by decide)) ?_
  · omega
  intro n5 p5 h5
  refine reaches_trans_budget n5 (actualPayloadHeaderAt 29) (actualPayloadHeaderAt 30) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 6 ?_ (by
      obtain ⟨bfValue, bfLocal, bfLength⟩ := p5.2.2
      refine storeWord n5 (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) 29 160
        (.op .add [.var .local (ofString "h"), .const (160#64)]) (.var .local (ofString "bf"))
        (actualPayloadHeaderAt 30) bfValue (flattenHOL bfValue) p5.1 p5.2.1 rfl rfl
        (actual_payload_header_eval_local_value n5 (ofString "bf") bfValue bfLocal) rfl ?_
      intro offset bound
      rw [bfLength] at bound
      interval_cases offset <;> bv_omega) ?_
  · omega
  intro n6 p6 h6
  refine reaches_trans_budget n6 (actualPayloadHeaderAt 30) (actualPayloadHeaderAt 31) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) ∧
        post.locals.lookup (ofString "wr") = some (.val (.word (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)))) ∧
        WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 2 4 ?_ (actual_payload_header_alloc_next_watched state n6 pl raw pointer (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (pointer + (136#64)) extraLen (ofString "wr") (32#64) (actualPayloadHeaderAt 31) p6.1 code (by decide) (by decide) (by decide) p6.2 (by omega)) ?_
  · omega
  intro n7 p7 h7
  refine reaches_trans_budget n7 (actualPayloadHeaderAt 31) (actualPayloadHeaderAt 32) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 4 ?_ (storeWord n7 (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) 31 192
      (.op .add [.var .local (ofString "h"), .const (192#64)]) (.var .local (ofString "wr"))
      (actualPayloadHeaderAt 32) (.val (.word (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)))) [HolWordLab.word (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64))] p7.1 p7.2.2 rfl rfl
      (actual_payload_header_eval_local n7 (ofString "wr") (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) p7.2.1) (by simp [flattenHOL]) (by intro offset bound; have zero := single offset bound; subst zero; simpa using actual_payload_header_pointer_cell_separate pointer 192 (by omega) (by omega))) ?_
  · omega
  intro n8 p8 h8
  refine reaches_trans_budget n8 (actualPayloadHeaderAt 32) (actualPayloadHeaderAt 33) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 4 ?_ (storeLoad n8 (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) 32 200 (.op .add [.var .local (ofString "pl"), .const (112#64)]) (actualPayloadHeaderAt 33) p8.1 p8.2 rfl (actual_payload_header_pointer_cell_separate pointer 200 (by omega) (by omega))) ?_
  · omega
  intro n9 p9 h9
  refine reaches_trans_budget n9 (actualPayloadHeaderAt 33) (actualPayloadHeaderAt 34) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 4 ?_ (storeLoad n9 (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) 33 208 (.op .add [.var .local (ofString "pl"), .const (120#64)]) (actualPayloadHeaderAt 34) p9.1 p9.2 rfl (actual_payload_header_pointer_cell_separate pointer 208 (by omega) (by omega))) ?_
  · omega
  intro n10 p10 h10
  refine reaches_trans_budget n10 (actualPayloadHeaderAt 34) (actualPayloadHeaderAt 35) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 4 ?_ (storeLoad n10 (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) 34 216 (.op .add [.var .local (ofString "si"), .const (24#64)]) (actualPayloadHeaderAt 35) p10.1 p10.2 rfl (actual_payload_header_pointer_cell_separate pointer 216 (by omega) (by omega))) ?_
  · omega
  intro n11 p11 h11
  refine reaches_trans_budget n11 (actualPayloadHeaderAt 35) (actualPayloadHeaderAt 36) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) ∧
        post.locals.lookup (ofString "rh") = some (.val (.word (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)))) ∧
        WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 2 2 ?_ (actual_payload_header_alloc_next_watched state n11 pl raw pointer (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (pointer + (136#64)) extraLen (ofString "rh") (32#64) (actualPayloadHeaderAt 36) p11.1 code (by decide) (by decide) (by decide) p11.2 (by omega)) ?_
  · omega
  intro n12 p12 h12
  refine reaches_trans_budget n12 (actualPayloadHeaderAt 36) (actualPayloadHeaderAt 37) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 2 ?_ (storeWord n12 (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) 36 224
      (.op .add [.var .local (ofString "h"), .const (224#64)]) (.var .local (ofString "rh"))
      (actualPayloadHeaderAt 37) (.val (.word (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)))) [HolWordLab.word (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64))] p12.1 p12.2.2 rfl rfl
      (actual_payload_header_eval_local n12 (ofString "rh") (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) p12.2.1) (by simp [flattenHOL]) (by intro offset bound; have zero := single offset bound; subst zero; simpa using actual_payload_header_pointer_cell_separate pointer 224 (by omega) (by omega))) ?_
  · omega
  intro n13 p13 h13
  refine reaches_trans_budget n13 (actualPayloadHeaderAt 37) (actualPayloadHeaderAt 38) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧
        post.locals.lookup (ofString "bh") = some (.val (.word (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)))) ∧
        WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 2 0 ?_ (actual_payload_header_alloc_next_watched state n13 pl raw pointer (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (pointer + (136#64)) extraLen (ofString "bh") (32#64) (actualPayloadHeaderAt 38) p13.1 code (by decide) (by decide) (by decide) p13.2 (by omega)) ?_
  · omega
  intro n14 p14 h14
  refine reaches_trans_budget n14 (actualPayloadHeaderAt 38) (actualPayloadHeaderAt 39) (actualPayloadHeaderAt 40)
    (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧
      WatchWord post (pointer + (136#64)) extraLen) (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧ WatchWord post (pointer + (136#64)) extraLen) 0 0 ?_ (storeWord n14 (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) 38 232
      (.op .add [.var .local (ofString "h"), .const (232#64)]) (.var .local (ofString "bh"))
      (actualPayloadHeaderAt 39) (.val (.word (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)))) [HolWordLab.word (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64))] p14.1 p14.2.2 rfl rfl
      (actual_payload_header_eval_local n14 (ofString "bh") (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) p14.2.1) (by simp [flattenHOL]) (by intro offset bound; have zero := single offset bound; subst zero; simpa using actual_payload_header_pointer_cell_separate pointer 232 (by omega) (by omega))) ?_
  · omega
  intro n15 p15 h15
  exact (storeLoad n15 (allocationEnd (allocationEnd (allocationEnd (allocationEnd (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) 39 240 (.op .add [.var .local (ofString "pl"), .const (128#64)]) (actualPayloadHeaderAt 40) p15.1 p15.2 rfl (actual_payload_header_pointer_cell_separate pointer 240 (by omega) (by omega)))

#print axioms actual_payload_header_construction_24_to_40_watched


end InitECandidate.Runtime

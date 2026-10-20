import InitECandidate.Runtime.ActualPayloadHeaderExtraLength
import InitECandidate.Runtime.FourWordStoreMemoryFrame
import InitECandidate.Runtime.NodedbWindowGeometry
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.WordStoreMemoryFrame

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

/-- **A watched word survives one actual header store.**  The store is the actual
`h[k] := value` of the header construction: the destination is the header cell `pointer + k` and the
value is a word, so only that cell changes and the watched word elsewhere is untouched. -/
theorem actual_payload_header_store_step_strong_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer heap watched cell : BitVec 64)
    (index k : Nat) (destination value : ExpHOL 64) (stored : BitVec 64) (tail : ProgHOL 64)
    (shape : actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (destShape : destination = .op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 k)])
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer heap)
    (valueEval : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) value = some (.val (.word stored)))
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
      have stored := evaluate_wordStore_memory_frame mid destination value
        (pointer + BitVec.ofNat 64 k) watched addressEval
        (by
          intro parsed evaluated
          exact ⟨stored,Option.some.inj (evaluated.symm.trans valueEval)⟩) separate
      rw [run] at stored
      exact stored
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
    (actual_payload_header_eval_word_const mid (1#64))
    (actual_payload_header_pl_cell_word_separate pl pointer 0 below cap (by omega)) watch with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · rcases actual_payload_header_store_step_strong_watched state E pl raw pointer
      (allocationEnd pointer (248#64)) (pl + (24#64)) extraLen 5 8 _ _ (raw + (0#64))
      (actualPayloadHeaderAt 6) source_actual_payload_header_store_raw rfl pE.1
      (actual_payload_header_eval_word_add E (ofString "raw") raw (0#64) pE.1.1.2.1)
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
        WatchWord post (pl + (24#64)) extraLen) 2 (actualPayloadHeaderAt 7) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_alloc_output]
  refine actual_payload_header_alloc_step mid (ofString "oh") (32#64) (allocationEnd pointer (248#64))
    (actualPayloadHeaderAt 7) _ baseFacts.2.2.2.1 (by rw [baseFacts.2.2.2.2.2]; exact code) budget ?_
  intro post memory domain postCode globals
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_,?_⟩
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

end InitECandidate.Runtime

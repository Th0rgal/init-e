/-
Copyright (c) 2025 Flamingo Ponderado Unipessoal LDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InitECandidate.Runtime.ActualPayloadHeaderConstruction
import InitECandidate.Runtime.KeccakWideFullCallBound

/-!
# A stronger actual payload-header prefix: the non-heap globals are untouched

The construction predicate `ActualPayloadHeaderPrefix` records the heap pointer global, the memory
domain and the code, but not the other globals.  The actual `keccak256(tmp, 1, oh)` call at statement
nine needs the `keccak_st` and `keccak_pad` globals of the entry state, so the prefix must also carry
the fact that every global except `heap_ptr` is left untouched.  This module adds that stronger
predicate and re-derives the prefix reach with it, additively: the existing predicate and every
existing theorem are unchanged.
-/

namespace InitECandidate.Runtime

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- **Every global other than `heap_ptr` is untouched.**  The construction only ever writes the heap
pointer global, so all other globals of the entry state are still readable with their entry values. -/
def HeapGlobalsFrame {F : Type} (entry mid : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ name : MlS, name ≠ ofString "heap_ptr" → mid.globals.lookup name = entry.globals.lookup name

/-- The frame is reflexive. -/
theorem HeapGlobalsFrame.refl {F : Type} (state : PanSemStateFiniteExact 64 F) :
    HeapGlobalsFrame state state := fun _ _ => rfl

#print axioms HeapGlobalsFrame.refl

/-- **The stronger prefix facts.**  The actual construction prefix facts together with the frame of
all non-heap globals. -/
def ActualPayloadHeaderBaseFacts {F : Type} (entry mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) : Prop :=
  ActualPayloadHeaderPrefix entry mid pl raw pointer heap ∧ HeapGlobalsFrame entry mid

/-- An allocation rebinds `heap_ptr` only, so it preserves the frame of all other globals. -/
theorem HeapGlobalsFrame.alloc {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (frame : HeapGlobalsFrame entry s) (heap size : BitVec 64)
    (post : PanSemStateFiniteExact 64 F)
    (globals : post.globals =
      (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap size))) s).globals) :
    HeapGlobalsFrame entry post := by
  intro name different
  rw [globals]
  by_cases h : (ofString "heap_ptr" = name)
  · exact absurd h.symm different
  · simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,h]
    exact frame name different

#print axioms HeapGlobalsFrame.alloc

/-- **The stronger prefix through the header allocation.**  The two actual loads and the actual
`alloc 248` for `h`, with the prefix facts *and* the frame of all non-heap globals. -/
theorem actual_payload_header_strong_prefix_reaches {F : Type}
    (state : PanSemStateFiniteExact 64 F)
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
      (ActualPayloadHeaderBaseFacts state · pl raw pointer (allocationEnd pointer (248#64))) 2
      (actualPayloadHeaderAt 3) := by
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
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
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

#print axioms actual_payload_header_strong_prefix_reaches

/-- **The stronger prefix through the actual `memzero(h, 248)`.**  The call zeroes the header block
and leaves every global -- in particular the heap pointer -- as it was, so the frame survives. -/
theorem actual_payload_header_strong_memzero {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd pointer (248#64)) ∧ ZeroBytePrefix post pointer 248) 251
      (actualPayloadHeaderAt 4) := by
  rcases actual_payload_header_strong_prefix_reaches state si pl raw pointer siLocal siDomain siCell
    plDomain plCell code heapGlobal (by omega) (by omega) with ⟨mid, typed, c1, c2, sc⟩ | ab
  · obtain ⟨baseFacts, frame⟩ := typed
    have sizeNat : (248#64).toNat = 248 := by decide
    have arguments : evalListHOLFinite mid
        (h := fun address => Classical.propDecidable (mid.memaddrs address))
        [.var .local (ofString "h"), .const (248#64)] =
        (some [ValueHOL.val (HolWordLab.word pointer), ValueHOL.val (HolWordLab.word (248#64))] :
          Option (List (ValueHOL 64))) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,baseFacts.2.2.1]
    have codeMid : mid.code = originalRuntimeCode := by
      rw [baseFacts.2.2.2.2.2]; exact code
    obtain ⟨post, run, zeroed, spent, kept, globals, postCode, domain, be, locals, occupied⟩ :=
      evaluate_memzero_aligned_call mid (.var .local (ofString "h")) (.const (248#64)) pointer (248#64)
        arguments codeMid (by omega) fits aligned
        (fun offset below => by rw [baseFacts.2.2.2.2.1]; exact wordDomain offset below)
        (fun offset below => by rw [baseFacts.2.2.2.2.1]; exact byteDomain offset below)
    have stage : Reaches mid (actualPayloadHeaderAt 3)
        (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
            (allocationEnd pointer (248#64)) ∧ ZeroBytePrefix post pointer 248) 249
        (actualPayloadHeaderAt 4) := by
      rw [source_actual_payload_header_memzero]
      refine reaches_seq mid (ProgHOL.call (some (none,none)) (ofString "memzero")
        [.var .local (ofString "h"), .const (248#64)]) (actualPayloadHeaderAt 4) 249 _ ?_
      refine Or.inl ⟨post, ?_, by omega, by omega, run⟩
      refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,zeroed⟩
      · rw [locals]; exact baseFacts.1
      · rw [locals]; exact baseFacts.2.1
      · rw [locals]; exact baseFacts.2.2.1
      · rw [globals]; exact baseFacts.2.2.2.1
      · rw [domain]; exact baseFacts.2.2.2.2.1
      · rw [postCode]; exact baseFacts.2.2.2.2.2
      · intro name different
        rw [globals]
        exact frame name different
    rcases stage with ⟨post, facts, s1, s2, sq⟩ | ab2
    · refine Or.inl ⟨post, facts, ?_, ?_, scoped_trans sc sq⟩
      · show state.clock ≤ post.clock + 251
        omega
      · show post.clock ≤ state.clock
        omega
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 2 251 (by omega) ab)

#print axioms actual_payload_header_strong_memzero

/-- A store keeps the frame: it changes memory only. -/
theorem actual_payload_header_store_frame_strong {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (frame : HeapGlobalsFrame state mid) :
    Reaches mid (.seq (.store destination value) tail)
      (ActualPayloadHeaderBaseFacts state · pl raw pointer heap) 0 tail := by
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · exact Or.inl ⟨{mid with memory:=memory},
      ⟨facts,fun name different => frame name different⟩,by simp,by simp,run⟩

#print axioms actual_payload_header_store_frame_strong

/-- A single header store step with the strong facts. -/
theorem actual_payload_header_store_step_strong {F : Type}
    (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (index : Nat) (tail : ProgHOL 64)
    (shape : ∃ destination value, actualPayloadHeaderAt index = .seq (.store destination value) tail)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (frame : HeapGlobalsFrame state mid) :
    Reaches mid (actualPayloadHeaderAt index)
      (ActualPayloadHeaderBaseFacts state · pl raw pointer heap) 0 tail := by
  obtain ⟨destination,value,rewrite⟩ := shape
  rw [rewrite]
  exact actual_payload_header_store_frame_strong state mid pl raw pointer heap destination value
    tail facts frame

#print axioms actual_payload_header_store_step_strong

/-- **The stronger prefix through both header stores.**  The actual `h[0] := 1` and
`h[8] := raw + 0`, which leave every global untouched. -/
theorem actual_payload_header_strong_stores {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd pointer (248#64))) :
    Reaches mid (actualPayloadHeaderAt 4)
      (ActualPayloadHeaderBaseFacts state · pl raw pointer (allocationEnd pointer (248#64))) 0
      (actualPayloadHeaderAt 6) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rcases actual_payload_header_store_step_strong state mid pl raw pointer
    (allocationEnd pointer (248#64)) 4 (actualPayloadHeaderAt 5)
    ⟨_,_,source_actual_payload_header_store_zero⟩ baseFacts frame with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · obtain ⟨baseE, frameE⟩ := pE
    rcases actual_payload_header_store_step_strong state E pl raw pointer
      (allocationEnd pointer (248#64)) 5 (actualPayloadHeaderAt 6)
      ⟨_,_,source_actual_payload_header_store_raw⟩ baseE frameE with
      ⟨G, pG, d1, d2, sd⟩ | ab2
    · exact Or.inl ⟨G, pG, by omega, by omega, scoped_trans sc sd⟩
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr ab

#print axioms actual_payload_header_strong_stores

/-- **The stronger prefix through the actual `alloc 32` for `oh`.** -/
theorem actual_payload_header_strong_alloc_oh {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd pointer (248#64)))
    (code : state.code = originalRuntimeCode)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 6)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd pointer (248#64)) (32#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64))))) 2
      (actualPayloadHeaderAt 7) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_alloc_output]
  refine actual_payload_header_alloc_step mid (ofString "oh") (32#64) (allocationEnd pointer (248#64)) (actualPayloadHeaderAt 7) _
    baseFacts.2.2.2.1 (by rw [baseFacts.2.2.2.2.2]; exact code) budget ?_
  intro post memory domain postCode globals
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_⟩
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

#print axioms actual_payload_header_strong_alloc_oh

/-- **The stronger prefix through the actual `alloc 8` for `tmp`.** -/
theorem actual_payload_header_strong_alloc_tmp {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd (allocationEnd pointer (248#64)) (32#64)))
    (ohLocal : mid.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
    (code : state.code = originalRuntimeCode)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 7)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") = some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))) 2
      (actualPayloadHeaderAt 8) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_alloc_tmp]
  refine actual_payload_header_alloc_step mid (ofString "tmp") (8#64) (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (actualPayloadHeaderAt 8) _
    baseFacts.2.2.2.1 (by rw [baseFacts.2.2.2.2.2]; exact code) budget ?_
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
  · exact HeapGlobalsFrame.alloc state mid frame (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64) post globals
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      ohLocal]
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms actual_payload_header_strong_alloc_tmp

/-- **The stronger prefix through the actual byte store `*(byte*)tmp := 192`.** -/
theorem actual_payload_header_strong_store_byte {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)))
    (ohLocal : mid.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))))
    (tmpLocal : mid.locals.lookup (ofString "tmp") = some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))) :
    Reaches mid (actualPayloadHeaderAt 8)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") = some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))) 0 (actualPayloadHeaderAt 9) := by
  obtain ⟨baseFacts, frame⟩ := facts
  rw [source_actual_payload_header_store_byte]
  have step := evaluate_storeByte_reaches mid (.var .local (ofString "tmp")) (.const (192#64))
    (actualPayloadHeaderAt 9)
  rcases step with ⟨post, ⟨g,l,c,d⟩, s1, s2, ssc⟩ | ab3
  · refine Or.inl ⟨post,⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,?_,?_⟩,by omega,by omega,ssc⟩
    · rw [l]; exact baseFacts.1
    · rw [l]; exact baseFacts.2.1
    · rw [l]; exact baseFacts.2.2.1
    · rw [g]; exact baseFacts.2.2.2.1
    · rw [d]; exact baseFacts.2.2.2.2.1
    · rw [c]; exact baseFacts.2.2.2.2.2
    · intro name different
      rw [g]
      exact frame name different
    · rw [l]; exact ohLocal
    · rw [l]; exact tmpLocal
  · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab3
    exact Or.inr ⟨x, h1, h2, by omega, by omega, fun k => h5 (by omega)⟩

#print axioms actual_payload_header_strong_store_byte

/-- **The stronger prefix, statement 0 to statement 9, for every outcome.**  The two actual loads,
the header allocation and the actual `memzero(h, 248)`, both header stores, the `oh` and `tmp`
allocations and the actual byte store, carrying the prefix facts together with the frame of all
non-heap globals and the two operand locals.  255 ticks, or abort. -/
theorem actual_payload_header_strong_prefix_0_to_9 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (si pl raw pointer : BitVec 64)
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
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer (allocationEnd (allocationEnd (allocationEnd pointer (248#64)) (32#64)) (8#64)) ∧
        post.locals.lookup (ofString "oh") = some (.val (.word (allocationEnd pointer (248#64)))) ∧
        post.locals.lookup (ofString "tmp") = some (.val (.word (allocationEnd (allocationEnd pointer (248#64)) (32#64))))) 255 (actualPayloadHeaderAt 9) := by
  rcases actual_payload_header_strong_memzero state si pl raw pointer siLocal siDomain siCell
    plDomain plCell code heapGlobal aligned fits wordDomain byteDomain (by omega) with
    ⟨E, ⟨prefixFacts, zeroed⟩, c1, c2, sc⟩ | ab
  · rcases actual_payload_header_strong_stores state E pl raw pointer prefixFacts with
      ⟨G, pG, d1, d2, sd⟩ | ab2
    · rcases actual_payload_header_strong_alloc_oh state G pl raw pointer pG
        code (by omega) with ⟨H, pH, e1, e2, se⟩ | ab3
      · rcases actual_payload_header_strong_alloc_tmp state H pl raw pointer
          pH.1 pH.2 code (by omega) with
          ⟨I, pI, f1, f2, sf⟩ | ab4
        · rcases actual_payload_header_strong_store_byte state I pl raw pointer
            pI.1 pI.2.1 pI.2.2 with ⟨J, pJ, g1, g2, sg⟩ | ab5
          · refine Or.inl ⟨J, pJ, by omega, by omega,
              scoped_trans sc (scoped_trans sd (scoped_trans se (scoped_trans sf sg)))⟩
          · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab5
            have ck := (scoped_trans sc (scoped_trans sd (scoped_trans se sf))).2.1
            exact Or.inr ⟨x, (scoped_trans sc (scoped_trans sd (scoped_trans se sf))).1.trans h1,
              h2, by omega, by omega, fun k => h5 (by omega)⟩
        · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab4
          have ck := (scoped_trans sc (scoped_trans sd se)).2.1
          exact Or.inr ⟨x, (scoped_trans sc (scoped_trans sd se)).1.trans h1, h2, by omega, by omega,
            fun k => h5 (by omega)⟩
      · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab3
        have ck := (scoped_trans sc sd).2.1
        exact Or.inr ⟨x, (scoped_trans sc sd).1.trans h1, h2, by omega, by omega,
          fun k => h5 (by omega)⟩
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact Or.inr ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono state _ 251 255 (by omega) ab)

#print axioms actual_payload_header_strong_prefix_0_to_9

/-- **The actual `keccak256(tmp, 1, oh)` call with the globals derived from the entry state.**  The
`keccak_st` and `keccak_pad` globals are read from the entry state and transported to the reached
state by the frame: the construction only ever rebinds `heap_ptr`. -/
theorem actual_payload_header_strong_keccak {F : Type} (ref state : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp st pad : BitVec 64)
    (facts : ActualPayloadHeaderCommit ref state pl raw pointer heap oh tmp)
    (frame : HeapGlobalsFrame ref state)
    (code : state.code = originalRuntimeCode)
    (stateGlobal : ref.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : ref.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (ticks : 360 ≤ state.clock)
    (stateSmall : st.toNat + 200 ≤ 33806089496) (stateAligned : st.toNat % 8 = 0)
    (stateWords : ∀ offset : Nat, offset < 200 → state.memaddrs (st + BitVec.ofNat 64 offset))
    (stateBytes : ∀ offset : Nat, offset < 200 →
      state.memaddrs (panByteAlignHOL (st + BitVec.ofNat 64 offset)))
    (small : pad.toNat + 136 ≤ 33806089496) (padAligned : pad.toNat % 8 = 0)
    (tmpAligned : tmp.toNat % 8 = 0) (ohAligned : oh.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 →
      state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < 1 → state.memaddrs (tmp + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < 1 →
      state.memaddrs (panByteAlignHOL (tmp + BitVec.ofNat 64 offset))) :
    Reaches state (actualPayloadHeaderAt 9)
      (ActualPayloadHeaderCommit ref · pl raw pointer heap oh tmp) 360 (actualPayloadHeaderAt 10) := by
  refine actual_payload_header_keccak_reaches ref state pl raw pointer heap oh tmp st pad facts code
    ?_ ?_ ticks stateSmall stateAligned stateWords stateBytes small padAligned tmpAligned ohAligned
    words bytes sourceWords sourceBytes
  · rw [frame (ofString "keccak_st") (by decide)]
    exact stateGlobal
  · rw [frame (ofString "keccak_pad") (by decide)]
    exact padGlobal

#print axioms actual_payload_header_strong_keccak

/-- **The outcome analysis of the keccak call.**  Given only a `RunBounded` budget for the actual
`keccak256(tmp, 1, oh)` call, every outcome is covered: a normal return re-establishes the whole
commit with the caller's locals restored and the globals and heap pointer untouched, and any other
result -- never a returned value, never a timeout -- falls in the abort branch. -/
theorem actual_payload_header_keccak_reaches_of_bounded {F : Type}
    (ref state : PanSemStateFiniteExact 64 F) (pl raw pointer heap oh tmp : BitVec 64)
    (facts : ActualPayloadHeaderCommit ref state pl raw pointer heap oh tmp)
    (code : state.code = originalRuntimeCode) (cost : Nat)
    (bounded : RunBounded state actualPayloadHeaderKeccak cost) :
    Reaches state (actualPayloadHeaderAt 9)
      (ActualPayloadHeaderCommit ref · pl raw pointer heap oh tmp) cost (actualPayloadHeaderAt 10) := by
  rw [source_actual_payload_header_keccak_shape]
  refine reaches_seq state actualPayloadHeaderKeccak (actualPayloadHeaderAt 10) cost _ ?_
  unfold RunBounded at bounded
  change state.clock ≤ (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock + cost ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 ≠ some .timeOut at bounded
  by_cases normal : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = none
  · obtain ⟨post,run⟩ : ∃ post : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState state actualPayloadHeaderKeccak = (none, post) :=
      ⟨_, by rw [Prod.eq_iff_fst_eq_snd_eq]; exact ⟨normal,rfl⟩⟩
    refine Or.inl ⟨post,?_,?_,?_,run⟩
    · exact actual_payload_header_commit_after_keccak ref state post pl raw pointer heap oh tmp
        facts code run
    · have spent := bounded.1
      rw [run] at spent
      exact spent
    · have kept := bounded.2.1
      rw [run] at kept
      exact kept
  · obtain ⟨x,run⟩ : ∃ result, (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = some result := by
      cases placed : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 with
      | none => exact absurd placed normal
      | some result => exact ⟨result,rfl⟩
    refine Or.inr ⟨x,run,?_,bounded.1,bounded.2.1,?_⟩
    · intro value returned
      have discard := evaluate_discard_call_no_return state (ofString "keccak256")
        [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] value
      exact discard (run.trans (congrArg some returned))
    · intro clock budget
      have different := bounded.2.2
      rw [run] at different
      exact different (congrArg some budget)

#print axioms actual_payload_header_keccak_reaches_of_bounded

/-- **The actual keccak call bounded by the canonical typed-only wide contract.**  Only the typed
`keccak_st`/`keccak_pad` globals of the entry state, the typed argument list and the output's
eight-byte alignment are needed; the operand workspace domains are not.  The wide bound is 145 ticks
and is weakened to the 360 the rest of the construction uses. -/
theorem actual_payload_header_strong_keccak_wide {F : Type} (ref state : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp st pad : BitVec 64)
    (facts : ActualPayloadHeaderCommit ref state pl raw pointer heap oh tmp)
    (frame : HeapGlobalsFrame ref state)
    (code : state.code = originalRuntimeCode)
    (stateGlobal : ref.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : ref.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (ohAligned : oh.toNat % 8 = 0) (ticks : 145 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 9)
      (ActualPayloadHeaderCommit ref · pl raw pointer heap oh tmp) 145 (actualPayloadHeaderAt 10) := by
  have one : (1#64 : BitVec 64).toNat = 1 := by decide
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] =
      (some [.val (.word tmp),.val (.word (1#64)),.val (.word oh)] : Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,facts.2.2,facts.2.1]
  have atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)) := by
    rw [frame (ofString "keccak_st") (by decide)]
    exact stateGlobal
  have atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
    rw [frame (ofString "keccak_pad") (by decide)]
    exact padGlobal
  have wide := runBounded_keccak_wide_full_call state st pad tmp (1#64) oh none
    [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")]
    atState atPad args (by decide) ohAligned code (by omega)
  have bounded : RunBounded state actualPayloadHeaderKeccak 145 := by
    have spent := wide.1
    rw [one] at spent
    refine ⟨?_,wide.2.1,wide.2.2⟩
    change state.clock ≤ (evaluateHOLFiniteState state (ProgHOL.call (some (none,none))
      (ofString "keccak256") [.var .local (ofString "tmp"), .const (1#64),
        .var .local (ofString "oh")])).2.clock + 145
    exact spent
  exact actual_payload_header_keccak_reaches_of_bounded ref state pl raw pointer heap oh tmp facts
    code 145 bounded

#print axioms actual_payload_header_strong_keccak_wide

end InitECandidate.Runtime

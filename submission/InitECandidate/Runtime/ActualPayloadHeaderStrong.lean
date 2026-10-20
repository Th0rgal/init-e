/-
Copyright (c) 2025 Flamingo Ponderado Unipessoal LDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InitECandidate.Runtime.ActualPayloadHeaderConstruction

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

end InitECandidate.Runtime

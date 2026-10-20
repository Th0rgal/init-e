import InitECandidate.Runtime.HeaderWithdrawalLoopStep
import InitECandidate.Runtime.RlpWindowCalls
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.CountedLoop
import InitECandidate.Runtime.StoreLoopWindow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The initial locals of a withdrawal encoder call: its single parameter `wd` bound to the record
addresss. -/
abbrev wdEncoderCallee (argumentWord : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "wd",ValueHOL.val (HolWordLab.word argumentWord))

/-- One full iteration of the withdrawal loop keeps every cell outside the two slice cells of that
iteration and outside the encoder's own 64-byte allocation window.  The encoder's returned tuple
supplies exactly the two stored words. -/
theorem wd_slice_step_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (slices counter argumentWord heapBase w : BitVec 64)
    (atCounter : t.locals.lookup (ofString "i") = some (.val (.word counter)))
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word heapBase)))
    (code : t.code = originalRuntimeCode) (clock : 3 ≤ t.clock)
    (heapBound : heapBase.toNat + 64 < 2^64)
    (out : ¬ MWin heapBase 64 w)
    (slice0 : w ≠ slices + counter * 16#64)
    (slice8 : w ≠ slices + (counter * 16#64 + 8#64))
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word argumentWord)]) :
    (evaluateHOLFiniteState t wdSliceLoopBody).2.memory w = t.memory w := by
  rw [wdSliceLoopBody]
  have installed : t.code.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd",.one)],sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp,
        .comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_encode_withdrawal_rlp_lookup
  have lookup := pan_single_word_lookup_shape t.code.lookup (ofString "encode_withdrawal_rlp")
    (ofString "wd") (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) argumentWord
    (.comb [.one,.one]) installed
  apply decCall_window t (ofString "e") (.comb [.one,.one]) (ofString "encode_withdrawal_rlp")
    [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
      .panop .mul [.var .local (ofString "i"), .const (44#64)]]]
    wdSliceLoopStores w [ValueHOL.val (HolWordLab.word argumentWord)]
    (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)
    (wdEncoderCallee argumentWord) (.comb [.one,.one]) hargs lookup
  · -- the encoder keeps the cell by its own window lemma
    have entryHeap : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).globals.lookup
          (ofString "heap_ptr") = some (.val (.word heapBase)) := by
      simpa [callEntryStateHOLFinite] using atHeap
    have entryWd : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).locals.lookup
          (ofString "wd") = some (.val (.word argumentWord)) := by
      simp [callEntryStateHOLFinite,wdEncoderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
    have entryCode : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).code =
        originalRuntimeCode := by
      simpa [callEntryStateHOLFinite] using code
    exact rlpEncodeWithdrawal_window _ heapBase argumentWord w entryHeap entryWd out heapBound entryCode
  · -- the stores keep the cell whatever the callee returned
    intro value base bodyRun shapeOk returnOk k
    obtain ⟨first,second,rfl⟩ := valueWords_of_comb shapeOk
    have entryHeap : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).globals.lookup
        (ofString "heap_ptr") = some (.val (.word heapBase)) := by
      simpa [callEntryStateHOLFinite] using atHeap
    have entryWd : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).locals.lookup
        (ofString "wd") = some (.val (.word argumentWord)) := by
      simp [callEntryStateHOLFinite,wdEncoderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
    have entryCode : (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).code =
        originalRuntimeCode := by
      simpa [callEntryStateHOLFinite] using code
    have entryClock : 2 ≤ (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)).clock := by
      simp only [callEntryStateHOLFinite]
      omega
    have baseSlices : base.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word slices)) := by
      have kept := rlpEncodeWithdrawal_other_globals
        (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)) base heapBase
        (.rStruct [.val (.word first),.val (.word second)]) (ofString "wd_rlp_slices")
        entryHeap entryCode entryClock (show ofString "wd_rlp_slices" ≠ ofString "heap_ptr" by decide)
        bodyRun
      rw [kept]
      simpa [callEntryStateHOLFinite] using atSlices
    have baseMemory : base.memory w = t.memory w := by
      have kept := rlpEncodeWithdrawal_window
        (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)) heapBase argumentWord w
        entryHeap entryWd out heapBound entryCode
      rw [bodyRun] at kept
      exact kept
    have slice8' : w ≠ slices + counter * 16#64 + 8#64 := by
      rw [BitVec.add_assoc]
      exact slice8
    have stores := wd_slice_stores_window (t := setVarHOLFinite (ofString "e")
      (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word first),ValueHOL.val (HolWordLab.word second)])
      {base with clock := k, locals := t.locals})
      slices counter first second w
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "e" ≠ ofString "i" by decide,atCounter])
      (by simpa [setVarHOLFinite] using baseSlices)
      (by
        change (setVarHOLFinite (ofString "e")
          (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word first),ValueHOL.val (HolWordLab.word second)])
          {base with clock := k, locals := t.locals}).locals.lookup (ofString "e") =
          some (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word first),ValueHOL.val (HolWordLab.word second)])
        simp only [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        rw [if_pos (show (ofString "e" == ofString "e") = true by decide)])
      slice0 slice8'
    rw [stores]
    exact baseMemory

/-- The statement-46 loop condition `i < nwd` is the *signed* comparison: for two words below
`2^63` it means exactly the unsigned comparison of their values. -/
theorem cond_less_small {F : Type} (s : PanSemStateFiniteExact 64 F) (I N v : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (hn : s.locals.lookup (ofString "nwd") = some (.val (.word N)))
    (smallI : I.toNat < 2 ^ 63) (smallN : N.toNat < 2 ^ 63)
    (hv : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) =
        some (.val (.word v))) :
    (v ≠ 0 ↔ I.toNat < N.toNat) := by
  rw [evalHOLFinite_eq_toExact] at hv
  have signed := holAsmSignedLess_small I N smallI smallN
  simp [evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL,signed] at hv
  constructor
  · intro nz
    by_cases c : I.toNat < N.toNat
    · exact c
    · simp [c] at hv
      exfalso
      exact nz hv.symm
  · intro lt
    simp [lt] at hv
    rw [← hv]
    decide

/-- The stores of one iteration are a counted step on `i` by one. -/
theorem wdSliceLoopStores_adv : AdvStep (ofString "i") (1#64) wdSliceLoopStores := by
  rw [wdSliceLoopStores]
  exact AdvStep.word _ _ (AdvStep.word _ _ AdvStep.advance)

/-- The stores of one iteration never change the globals. -/
theorem wd_slice_stores_globals_frame : OriginalGlobalsFrame wdSliceLoopStores := by
  rw [wdSliceLoopStores]
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · apply originalGlobalsFrame_sequence
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

#print axioms wd_slice_stores_globals_frame

/-- Successor facts for one withdrawal loop iteration: on the normal path the counter advances by
one, `nwd`/`pl`/the result variable are untouched, and the heap pointer moves to the end of the
iteration's 64-byte encoder buffer. -/
theorem wd_slice_step_successor {F : Type} (t : PanSemStateFiniteExact 64 F)
    (I nwd pl slices heapBase argumentWord first second : BitVec 64)
    (st : PanSemStateFiniteExact 64 F)
    (atCounter : t.locals.lookup (ofString "i") = some (.val (.word I)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (.val (.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (.val (.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word heapBase)))
    (code : t.code = originalRuntimeCode) (clock : 3 ≤ t.clock)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word argumentWord)])
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite t
        (HolFiniteMapExact.empty.update (ofString "wd",ValueHOL.val (HolWordLab.word argumentWord))))
      (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned (.rStruct [.val (.word first),.val (.word second)])),st))
    (shapeOk : shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word first),.val (.word second)]))
      (.comb [.one,.one]) = true)
    (normal : (evaluateHOLFiniteState t wdSliceLoopBody).1 = none) :
    (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "i") =
        some (.val (.word (I + 1#64))) ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "nwd") =
        some (.val (.word nwd)) ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "pl") =
        some (.val (.word pl)) ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "e") = none ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.globals.lookup (ofString "wd_rlp_slices") =
        some (.val (.word slices)) ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationEnd heapBase 64))) := by
  have installed : t.code.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd",.one)],sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp,
        .comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_encode_withdrawal_rlp_lookup
  have lookup := pan_single_word_lookup_shape t.code.lookup (ofString "encode_withdrawal_rlp")
    (ofString "wd") (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) argumentWord
    (.comb [.one,.one]) installed
  have entryHeap : (callEntryStateHOLFinite t
      (HolFiniteMapExact.empty.update (ofString "wd",ValueHOL.val (HolWordLab.word argumentWord)))).globals.lookup
        (ofString "heap_ptr") = some (.val (.word heapBase)) := by
    simpa [callEntryStateHOLFinite] using atHeap
  have entryCode : (callEntryStateHOLFinite t
      (HolFiniteMapExact.empty.update (ofString "wd",ValueHOL.val (HolWordLab.word argumentWord)))).code =
      originalRuntimeCode := by
    simpa [callEntryStateHOLFinite] using code
  have entryClock : 2 ≤ (callEntryStateHOLFinite t
      (HolFiniteMapExact.empty.update (ofString "wd",ValueHOL.val (HolWordLab.word argumentWord)))).clock := by
    simp only [callEntryStateHOLFinite]
    omega
  have stCode : st.code = originalRuntimeCode := by
    have metadata := evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "wd",
        ValueHOL.val (HolWordLab.word argumentWord))))
      (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)
    rw [bodyRun] at metadata
    exact metadata.1.trans entryCode
  have baseSlices : st.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word slices)) := by
    have kept := rlpEncodeWithdrawal_other_globals
      (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "wd",
        ValueHOL.val (HolWordLab.word argumentWord)))) st heapBase
      (.rStruct [.val (.word first),.val (.word second)]) (ofString "wd_rlp_slices")
      entryHeap entryCode entryClock (show ofString "wd_rlp_slices" ≠ ofString "heap_ptr" by decide) bodyRun
    rw [kept]
    simpa [callEntryStateHOLFinite] using atSlices
  have baseHeap : st.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd heapBase 64))) :=
    rlpEncodeWithdrawal_heap
      (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "wd",
        ValueHOL.val (HolWordLab.word argumentWord)))) st heapBase
      (.rStruct [.val (.word first),.val (.word second)]) entryHeap entryCode entryClock bodyRun
  set contState : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "e") (.rStruct [.val (.word first),.val (.word second)])
      { st with
        locals := t.locals
        clock := (if (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "wd",
            ValueHOL.val (HolWordLab.word argumentWord)))).clock < st.clock then
          (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "wd",
            ValueHOL.val (HolWordLab.word argumentWord)))).clock else st.clock) } with contStateDef
  have binding : contState.locals.lookup (ofString "i") = some (.val (.word I)) := by
    rw [contStateDef]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "e" ≠ ofString "i" by decide,atCounter]
  obtain ⟨result,advanced,stepRun,frame,normalRec⟩ :=
    evaluate_advStep wdSliceLoopStores_adv contState I binding
  have contCode : contState.code = originalRuntimeCode := by
    rw [contStateDef]; exact stCode
  have globalsKept : advanced.globals = st.globals := by
    have carried := wd_slice_stores_globals_frame _ contCode
    rw [stepRun] at carried
    exact carried
  set entryPair : MlS × Option (ValueHOL 64) := (ofString "e",t.locals.lookup (ofString "e")) with entryPairDef
  have pairNone : entryPair.2 = none := by
    rw [entryPairDef]; exact freshE
  have bodyEq : evaluateHOLFiniteState t wdSliceLoopBody =
      (result, {advanced with locals := HolFiniteMapExact.resVarEq advanced.locals entryPair}) := by
    rw [wdSliceLoopBody,evaluateHOLFiniteState_decCall_total,hargs]
    dsimp only
    rw [lookup]
    dsimp only
    rw [if_neg (by omega)]
    rw [bodyRun]
    dsimp only [fixClockHOLFinite]
    simp only [shapeOk,Bool.and_self,if_true,ite_true]
    rw [← contStateDef]
    rw [stepRun]
  rw [bodyEq] at normal
  cases normal
  have hi : advanced.locals.lookup (ofString "i") = some (.val (.word (I + 1#64))) := by
    rcases normalRec with ⟨-,h⟩ | h
    · exact h
    · cases h
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [bodyEq]
    rw [entryPairDef,freshE]
    simp only [HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL]
    exact hi
  · rw [bodyEq]
    rw [entryPairDef,freshE]
    simp only [HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL]
    rw [frame (ofString "nwd") (show ofString "nwd" ≠ ofString "i" by decide)]
    exact atNwd
  · rw [bodyEq]
    rw [entryPairDef,freshE]
    simp only [HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL]
    rw [frame (ofString "pl") (show ofString "pl" ≠ ofString "i" by decide)]
    exact atPl
  · rw [bodyEq]
    rw [entryPairDef,freshE]
    simp [HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL]
  · rw [bodyEq]
    simp only [globalsKept]
    exact baseSlices
  · rw [bodyEq]
    simp only [globalsKept]
    exact baseHeap

#print axioms wd_slice_step_successor

#print axioms cond_less_small

#print axioms wd_slice_step_window
end InitECandidate.Runtime

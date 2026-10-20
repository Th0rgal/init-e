import InitECandidate.Runtime.SourceCostPipelineFacts
import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-! The end-to-end transfer instantiated at the initial states of the pinned
`pan_to_word` `state_rel_imp_semantics` proof: the `pan_globals` target state,
`crepStateHOL` and `loopStateHOL`, built from the source state and the Word
target state. -/

/-- The `pan_globals` target state of the pinned proof, at the given clock. -/
noncomputable def initialGlobalState {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (globalsSize clock : Nat) : PanSemStateFiniteExact 64 F :=
  { ({ source with clock := clock } : PanSemStateFiniteExact 64 F) with
    topAddr := source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize
    memaddrs := fun address => source.memaddrs address ∨
      Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
    memory := wlocWlabHOL ∘ target.memory
    locals := source.locals }

theorem initial_globals_premises {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (code : List (DeclHOL 64)) (globalsSize clock : Nat)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address))
    (hstc : decsStcnamesHOLExact (width := 64) [] code = some [])
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact (width := 64) [] code)))).sum)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (halloc : globalsAllocatableHOL source code)
    (hcode : source.code = HolFiniteMapExact.empty) (hglobals : source.globals = HolFiniteMapExact.empty)
    (hdim : goodDimindex 64)
    (structFree : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code) =
      panSimpDeclsHOL code) :
    ((functionsHOL (panSimpDeclsHOL code)).map Prod.fst).Nodup ∧
      initialGlobalState source target globalsSize clock =
        { ({ source with clock := clock } : PanSemStateFiniteExact 64 F) with
          topAddr := source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize
          memaddrs := fun address => source.memaddrs address ∨
            Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
          memory := wlocWlabHOL ∘ target.memory
          locals := source.locals } ∧
      source.code = HolFiniteMapExact.empty ∧
      source.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL source.topAddr ∧
      goodDimindex 64 ∧
      panBytesInWord 64 * BitVec.ofNat 64 globalsSize = panBytesInWord 64 *
        BitVec.ofNat 64 ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum ∧
      Compiler.Backend.StackRemove.addresses source.topAddr globalsSize =
        Compiler.Backend.StackRemove.addresses source.topAddr
          ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum ∧
      (∀ address, source.memaddrs address →
        ¬ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (∀ address, source.memaddrs address → source.memory address = (wlocWlabHOL ∘ target.memory) address) ∧
      ¬ source.memaddrs (source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize) ∧
      (panBytesInWord 64).toNat * ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum < 2 ^ 64 ∧
      (∀ d ∈ panSimpDeclsHOL code,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) := by
  have hsizePlain : ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum = globalsSize := by
    rw [hsize, decShapesCompileProgHOL, hstc]
    simp only [holThe]
    congr 1
    apply List.map_congr_left
    intro shape _
    exact (sharp_size_nil shape).symm
  have halloc' := halloc
  dsimp only [globalsAllocatableHOL] at halloc'
  rw [← hsize] at halloc'
  obtain ⟨_, hdisjoint, htopnot, hbound⟩ := halloc'
  refine ⟨?_, rfl, hcode, hglobals, halign, hdim, by rw [hsizePlain], by rw [hsizePlain],
    fun address hs hf => hdisjoint address ⟨hs, hf⟩, ?_, htopnot, ?_, ?_⟩
  · rw [← structFree, functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  · intro address ha
    simp only [Function.comp_apply, hmem address ha, wlocWlabWlabWlocHOL]
  · simpa [hsizePlain, panBytesInWord, Compiler.Backend.StackRemove.bytesInWord, Nat.mul_comm] using hbound
  · rw [← structFree]; exact Pancake.PanStructs.CompileShapeExact.compileTopNoNames _

#print axioms initial_globals_premises

/-- The installed-entry premises at the pinned initial states, for the actual
post-declaration state `T` of the compiled program. -/
theorem initial_entry_pipeline {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (arch : AsmArchitecture) (code : List (DeclHOL 64))
    (start : MlS) (globalsSize clock : Nat)
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (hmdomain : (fun address => target.mdomain address = true) =
      (fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address))
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (hcode : source.code = HolFiniteMapExact.empty) (hglobals : source.globals = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL code < 2 ^ 64)
    (heshapes : source.eshapes = HolFiniteMapExact.empty)
    (structFree : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code) =
      panSimpDeclsHOL code)
    (body : ProgHOL 64) (rshape : ShapeHOL)
    (hmain : List.lookup start (functionsHOL (panSimpDeclsHOL code)) = some ([], body, rshape))
    (noInline : (functionsHOL ((compileTopExactHOL (panSimpDeclsHOL code) start).filter inlinableHOL)).map
      Prod.fst = [])
    (sites : ∀ entry ∈ functionsHOL (compileTopExactHOL (panSimpDeclsHOL code) start),
      sharpSitesProg sharpReplayBound entry.2.2.1 = true)
    (startProgram : CrepProgHOL 64)
    (hsp : holAlookup (compileProgDeclsHOLW (compileTopExactHOL (panSimpDeclsHOL code) start)) start =
      some ([], startProgram))
    {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @evaluateDeclsHOLFinite 64 F _ { source with structs := [] }
      (fun a => Classical.propDecidable (source.memaddrs a)) (panSimpDeclsHOL code) = some s1)
    (T : PanSemStateFiniteExact 64 F)
    (hT : @evaluateDeclsHOLFinite 64 F _ { initialGlobalState source target globalsSize clock with structs := [] }
      (fun a => Classical.propDecidable ((initialGlobalState source target globalsSize clock).memaddrs a))
      (compileTopExactHOL (panSimpDeclsHOL code) start) = some T) :
    let G := initialGlobalState source target globalsSize clock
    let panCode := compileTopExactHOL (panSimpDeclsHOL code) start
    let crepState := crepStateHOL G panCode G.memory
    EntryPipeline arch panCode start startProgram T crepState
      (loopStateHOL crepState arch (compileProgDeclsHOLW panCode) target.clock target.memory) := by
  intro G panCode crepState
  have hdiststruct : ((functionsHOL (panSimpDeclsHOL code)).map Prod.fst).Nodup := by
    rw [← structFree, functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  have hkinds : ∀ d ∈ panSimpDeclsHOL code,
      isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true := by
    rw [← structFree]; exact Pancake.PanStructs.CompileShapeExact.compileTopNoNames _
  have hT' := PanGlobalsCompileTopSemanticsDecls.evaluateCompileTopOfSource _ s1 { G with structs := [] } (panSimpDeclsHOL code) start _ hs1
    hmain hkinds rfl (by simp [G, initialGlobalState])
  rw [hT'] at hT
  have hTform := (Option.some.inj hT).symm
  have hdistPan : ((functionsHOL panCode).map Prod.fst).Nodup := by
    have := allDistinctCompileTopHOL start (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact
      (panSimpDeclsHOL code)) (by rw [structFree]; exact hdiststruct)
    rw [structFree] at this; exact this
  have hpanSize : sizeOfEidsHOL panCode < 2 ^ 64 := by
    have h := sizeOfEidsCompileTopHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact
      (panSimpDeclsHOL code)) start [] body rshape (by rw [structFree]; exact hmain)
    rw [structFree] at h
    show sizeOfEidsHOL (compileTopExactHOL (panSimpDeclsHOL code) start) < _
    rw [h, ← structFree, sizeOfEidsStructsCompileEqHOL, sizeOfEidsHOL_panSimpDeclsHOL_eq]
    exact heids
  subst hTform
  refine
    { state := ?_
      distinct := hdistPan
      sourceCode := ?_
      noInline := noInline
      emptyLocals := ?_
      localised := ?_
      eidsSize := hpanSize
      eidsDomain := ?_
      memaddrs := by simp [loopStateHOL]
      be := rfl
      shMemaddrs := by simp [loopStateHOL]
      ffi := rfl
      baseAddr := rfl
      topAddr := rfl
      memory := ?_
      globals := ?_
      crepDistinct := panToCrepFirstCompileProgAllDistinctExact panCode hdistPan
      crepCode := rfl
      loopCode := rfl
      crepLocals := rfl
      startLookup := hsp
      sites := sites }
  · simp [panToCrepStateRelFiniteExact, crepState, crepStateHOL, G, initialGlobalState, hglobals,
      HolFiniteMapExact.empty]
  · show (HolFiniteMapExact.updateList G.code (functionsHOL panCode)) = _
    simp only [G, initialGlobalState, hcode]
    exact pipeline_code_reverse panCode hdistPan
  · simp [G, initialGlobalState, hlocals]
  · have := compileTopLocalisedHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact
      (panSimpDeclsHOL code)) start
    rw [structFree] at this; exact this
  · intro key
    show ((HolFiniteMapExact.updateList G.eshapes (exceptionsHOL panCode)).lookup key).isSome = _
    simp only [G, initialGlobalState, heshapes]
    exact pipeline_eids_domain panCode key
  · intro address ha
    have ha' : target.mdomain address = true := by
      exact (congrFun hmdomain address).symm ▸ ha
    obtain ⟨w, hw⟩ := hnolabels address ha'
    simp [crepState, crepStateHOL, G, initialGlobalState, loopStateHOL, wlocWlabHOL, wlabWlocExact, hw]
  · intro address value he
    simp [crepState, crepStateHOL, HolFiniteMapExact.empty] at he

#print axioms initial_entry_pipeline

/-- End-to-end transfer at the pinned `pan_to_word` initial states: the
original entry run from the post-declaration state of the original declarations
(at any clock) is matched by the installed Loop entry from `loopStateHOL`, with
Loop work at most the sharp score of the original canonical events plus the
one-time `pan_globals` initialiser cost. -/
theorem source_loop_initial {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (arch : AsmArchitecture) (code : List (DeclHOL 64))
    (start : MlS) (globalsSize clock : Nat)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address))
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (hstc : decsStcnamesHOLExact (width := 64) [] code = some [])
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact (width := 64) [] code)))).sum)
    (hmdomain : (fun address => target.mdomain address = true) =
      (fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address))
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (halloc : globalsAllocatableHOL source code)
    (hcode : source.code = HolFiniteMapExact.empty) (hglobals : source.globals = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL code < 2 ^ 64)
    (heshapes : source.eshapes = HolFiniteMapExact.empty) (hdim : goodDimindex 64)
    (structFree : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code) =
      panSimpDeclsHOL code)
    (body : ProgHOL 64) (rshape : ShapeHOL)
    (hmain : List.lookup start (functionsHOL (panSimpDeclsHOL code)) = some ([], body, rshape))
    (ready : ∀ entry ∈ functionsHOL (panSimpDeclsHOL code),
      globalsReadyProg entry.2.2.1 = true ∧ globalsTemp ∉ entry.2.1.map Prod.fst)
    (constGlobals : constGlobalDecls ((panSimpDeclsHOL code).filter isDeclHOL) = true)
    (noInline : (functionsHOL ((compileTopExactHOL (panSimpDeclsHOL code) start).filter inlinableHOL)).map
      Prod.fst = [])
    (sites : ∀ entry ∈ functionsHOL (compileTopExactHOL (panSimpDeclsHOL code) start),
      sharpSitesProg sharpReplayBound entry.2.2.1 = true)
    {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @evaluateDeclsHOLFinite 64 F _ { source with structs := [] }
      (fun a => Classical.propDecidable (source.memaddrs a)) code = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F} {ev : List WorkEvent}
    (run : StatementRun { s1 with clock := clock } (.call none start []) r post ev)
    (ok : r ≠ some .error) :
    let G := initialGlobalState source target globalsSize clock
    let panCode := compileTopExactHOL (panSimpDeclsHOL code) start
    let crepState := crepStateHOL G panCode G.memory
    let loopState := loopStateHOL crepState arch (compileProgDeclsHOLW panCode) target.clock target.memory
    let program := crepSimpProgHOL (compileProgExactHOLW (entryPanContext panCode) (.call none start []))
    let loopProgram := compileHOLExact (entryLoopContext arch panCode) .ln program
    ∃ T, @evaluateDeclsHOLFinite 64 F _ { G with structs := [] }
        (fun a => Classical.propDecidable (G.memaddrs a)) panCode = some T ∧
      ∃ extra wl,
        LoopWork { loopState with clock := T.clock + 1 + extra } loopProgram
          (evaluate loopProgram { loopState with clock := T.clock + 1 + extra }) wl ∧
        wl ≤ sharpScore ev +
          globalsTopInit rshape ((panSimpDeclsHOL code).filter isDeclHOL).length (callPayloadWords r) ∧
        LoopRunRel (entryLoopContext arch panCode) .ln
          (evalCrepSemHOLProgExact (crepSimpMapcsHOL { crepState with clock := T.clock + 1 }) program)
          (evaluate loopProgram { loopState with clock := T.clock + 1 + extra }) := by
  intro G panCode crepState loopState program loopProgram
  -- The simplified declarations evaluate (pinned pan_simp declaration relation).
  have relCode : PanSimp.CodeRel ({ source with structs := [] } : PanSemStateFiniteExact 64 F).code
      source.code := by
    refine ⟨fun f h => h, ?_⟩
    intro f vshs prog rshape' h
    rw [show ({ source with structs := [] } : PanSemStateFiniteExact 64 F).code = source.code from rfl,
      hcode] at h
    cases h
  obtain ⟨c', hev, -⟩ := PanSimp.evaluateDeclsCodeRel code { source with structs := [] } _ source.code s1
    relCode hs1
  obtain ⟨startProgram, hsp⟩ := pipeline_start_lookup (panSimpDeclsHOL code) start body rshape hmain
  exact source_loop_top code start source G clock _ _ _ _
    (initial_globals_premises source target code globalsSize clock hmem hstc hsize hdist halign halloc
      hcode hglobals hdim structFree)
    structFree body rshape hmain ready constGlobals arch startProgram crepState loopState
    (fun T hT => initial_entry_pipeline source target arch code start globalsSize clock hnolabels hmdomain
      hdist hcode hglobals hlocals heids heshapes structFree body rshape hmain noInline sites
      startProgram hsp hev T hT)
    hs1 run ok

#print axioms source_loop_initial
end InitECandidate.Runtime.FineCost

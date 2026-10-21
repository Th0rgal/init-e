import InitECandidate.Runtime.GuestCostSourceLoop
import InitECandidate.Runtime.GuestCostEntryShapes
import InitECandidate.Runtime.SourceCostInitial
import InitECandidate.Proofs.AllocationFacts
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open InitE InitECandidate.Proofs.FrontendStages
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! The guest's end-to-end source → Loop transfer: the original `main` run
after the authoritative declarations (`Guest.guestAst.map declToHOL` from
`sourceInitialState input`) is matched by the installed Loop entry at its
sharp score plus the one-time additive initialiser `25061`. The Word-side
memory, label and domain facts remain explicit hypotheses. -/

/-- The entry's payload is at most one word. -/
theorem guest_entry_payload {s1 post : PanSemStateFiniteExact 64 Guest.HostMemory} {clock : Nat}
    {input : Guest.InputBlob}
    (hs1 : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { sourceInitialState input with structs := [] }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) InitE.sourceDeclarations =
        some s1)
    {r ev} (run : StatementRun fn { s1 with clock := clock } (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [])
      r post ev) (ok : r ≠ some .error) : callPayloadWords r ≤ 1 := by
  have hcode := @evaluateDeclsHOLFinite_functions 64 Guest.HostMemory _ _
    (fun a => Classical.propDecidable _) _ s1 hs1
  refine entry_payload_le run ok ?_ ?_
  · intro body callee returnShape lookup
    obtain ⟨vshapes, hsrc, -⟩ :=
      lookupCodeHOLFinite_some_inv _ _ _ body callee returnShape lookup
    change s1.code.lookup _ = _ at hsrc
    rw [hcode, show functionsHOL InitE.sourceDeclarations =
      (functionsHOL InitE.sourceDeclarations).reverse.reverse by simp] at hsrc
    have mem := List.mem_reverse.1 (entry_code_mem hsrc)
    have := List.all_eq_true.1 guest_source_main_return _ mem
    simpa using this
  · intro eid shape found
    rcases decls_eshapes_mem _ _ s1 hs1 eid shape found with h | mem
    · simp [sourceInitialState, HolFiniteMapExact.empty] at h
    · have := List.all_eq_true.1 guest_source_exn_shapes _ mem
      simpa using this

/-- The source entry's call carries no WordSimp site surcharge. -/
theorem guest_entry_sites :
    callSites (Flapjack.Basis.Pure.MlString.ofString "main") freshEntryName = 0 := by decide +kernel

/-- Guest source → Loop transfer from the authoritative source program. -/
theorem guest_source_loop (input : Guest.InputBlob) {C : Type}
    (target : WordSemStateFiniteExact 64 C Guest.HostMemory) (arch : AsmArchitecture) (clock : Nat)
    (hmem : ∀ address, (sourceInitialState input).memaddrs address →
      target.memory address = wlabWlocExact ((sourceInitialState input).memory address))
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (hmdomain : (fun address => target.mdomain address = true) =
      (fun address => (sourceInitialState input).memaddrs address ∨
        Compiler.Backend.StackRemove.addresses (sourceInitialState input).topAddr guestGlobalsSize address))
    {s1 : PanSemStateFiniteExact 64 Guest.HostMemory}
    (hs1 : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { sourceInitialState input with structs := [] }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      (Guest.guestAst.map declToHOL) = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {ev : List WorkEvent}
    (run : StatementRun fn { s1 with clock := clock } (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [])
      r post ev)
    (ok : r ≠ some .error) :
    let start := Flapjack.Basis.Pure.MlString.ofString "main"
    let G := initialGlobalState (sourceInitialState input) target guestGlobalsSize clock
    let panCode := compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) start
    let crepState := crepStateHOL G panCode G.memory
    let loopState := loopStateHOL crepState arch (compileProgDeclsHOLW panCode) target.clock target.memory
    let program := crepSimpProgHOL (compileProgExactHOLW (entryPanContext panCode) (.call none start []))
    let loopProgram := compileHOLExact (entryLoopContext arch panCode) .ln program
    ∃ T, @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { G with structs := [] }
        (fun a => Classical.propDecidable (G.memaddrs a)) panCode = some T ∧
      ∃ extra wl,
        LoopWork { loopState with clock := T.clock + 1 + extra } loopProgram
          (evaluate loopProgram { loopState with clock := T.clock + 1 + extra }) wl ∧
        wl ≤ sharpScore ev + 25061 ∧
        LoopRunRel (entryLoopContext arch panCode) .ln
          (evalCrepSemHOLProgExact (crepSimpMapcsHOL { crepState with clock := T.clock + 1 }) program)
          (evaluate loopProgram { loopState with clock := T.clock + 1 + extra }) ∧
        (evaluate loopProgram { loopState with clock := T.clock + 1 + extra }).1 ≠ some .error := by
  intro start G panCode crepState loopState program loopProgram
  -- The compiler's main-first declarations evaluate to the same state.
  have hs1' : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { sourceInitialState input with structs := [] }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) InitE.sourceDeclarations =
        some s1 := by
    rw [InitECandidate.Runtime.original_declaration_evaluation]; exact hs1
  obtain ⟨body, rshape, hmain, hsz⟩ := guest_main_lookup
  have ready : ∀ entry ∈ functionsHOL (panSimpDeclsHOL InitE.sourceDeclarations),
      globalsReadyProg entry.2.2.1 = true ∧ globalsTemp ∉ entry.2.1.map Prod.fst := by
    intro entry mem
    rw [guest_simplified_eq_pass1] at mem
    obtain ⟨f, hf, rfl⟩ := guest_mem_functions mem
    exact guest_globals_body_ready f hf
  have constGlobals : constGlobalDecls ((panSimpDeclsHOL InitE.sourceDeclarations).filter isDeclHOL) = true := by
    rw [guest_simplified_eq_pass1]; exact guest_pass1_const_globals
  have noInline : (functionsHOL ((compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) start).filter
      inlinableHOL)).map Prod.fst = [] := by
    rw [guest_entry_program]; exact guest_pass2_no_inline_local
  have sites : ∀ entry ∈ functionsHOL (compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) start),
      sharpSitesProg sharpReplayBound entry.2.2.1 = true := by
    intro entry mem
    rw [guest_entry_program] at mem
    obtain ⟨f, hf, rfl⟩ := guest_mem_functions mem
    exact List.all_eq_true.1 guest_pass2_sharp_sites _ hf
  have hfresh : newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations) = freshEntryName := by
    rw [guest_simplified_eq_pass1]; kernel_rfl
  have hlabels : LabelInvariant (Flapjack.Basis.Pure.MlString.ofString "main")
      (newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations)) := by
    rw [hfresh]; exact labelInvariant_entry
  have entryMoves : callMoves (Flapjack.Basis.Pure.MlString.ofString "main")
      (newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations)) = 0 := by
    rw [hfresh]; decide +kernel
  have entrySites : callSites (Flapjack.Basis.Pure.MlString.ofString "main")
      (newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations)) = 0 := by
    rw [hfresh]; exact guest_entry_sites
  obtain ⟨T, hT, extra, wl, work, bound, rel, loopOk⟩ := source_loop_initial (sourceInitialState input) target arch
    InitE.sourceDeclarations start guestGlobalsSize clock hmem hnolabels guest_source_struct_context rfl
    hmdomain guest_source_distinct (guest_source_aligned input) (source_globals_allocatable input)
    rfl rfl rfl guest_source_eids rfl (Or.inr rfl)
    (compileTop_structFree _ guest_simplified_struct_free) body rshape hmain hlabels ready constGlobals noInline
    sites hs1' run ok
  refine ⟨T, hT, extra, wl, work, ?_, rel, loopOk⟩
  have payload := guest_entry_payload hs1' run ok
  have count : ((panSimpDeclsHOL InitE.sourceDeclarations).filter isDeclHOL).length = 93 := by
    rw [guest_simplified_eq_pass1]; exact guest_pass1_global_count
  rw [count] at bound
  have entryMoves' : callMoves start (newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations)) = 0 :=
    entryMoves
  have entrySites' : callSites start (newMainNameHOL (panSimpDeclsHOL InitE.sourceDeclarations)) = 0 :=
    entrySites
  simp only [globalsTopInit, hsz] at bound
  omega

#print axioms guest_entry_payload
#print axioms guest_source_loop
#print axioms guest_entry_sites
end InitECandidate.Runtime.FineCost

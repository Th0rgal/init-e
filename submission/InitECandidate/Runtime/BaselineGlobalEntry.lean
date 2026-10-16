import InitECandidate.Runtime.PanInitCallClock
import InitECandidate.Runtime.CanonicalPanNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def baselineRenamedMainBody : ProgHOL 64 :=
  match FrontendStages.Declarations.globalOutput0 with | .function decl => decl.body | _ => .skip

theorem baseline_pan_generated_main (input : Guest.InputBlob) :
    (canonicalPanEntryState input).code.lookup baselineCrepStart = some ([],
      .seq (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
        (.call none FrontendStages.Declarations.globalNewStart []),.one) := by
  calc
    _ = List.lookup baselineCrepStart (functionsHOL FrontendStages.pass2) :=
      FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by kernel_rfl

theorem baseline_pan_renamed_main (input : Guest.InputBlob) :
    (canonicalPanEntryState input).code.lookup FrontendStages.Declarations.globalNewStart =
      some ([],baselineRenamedMainBody,.one) := by
  calc
    _ = List.lookup FrontendStages.Declarations.globalNewStart (functionsHOL FrontendStages.pass2) :=
      FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by
      have name : (match FrontendStages.Declarations.globalOutput0 with
        | .function decl => decl.name | _ => baselineCrepStart) =
          FrontendStages.Declarations.globalNewStart := by decide_cbv
      simp only [FrontendStages.pass2, FrontendStages.Declarations.exceptionDeclarations,
        FrontendStages.generatedMain, FrontendStages.Declarations.translatedFunctions,
        functionsHOL, List.lookup, baselineRenamedMainBody]
      simp_all only [FrontendStages.Declarations.globalOutput0, declToHOL, funDeclToHOL,
        FrontendStages.Declarations.globalData0, List.map_nil, shapeToHOL]
      kernel_rfl

/-- Concrete generated global-initialization wrapper uses exactly one more
clock than its renamed entry run. Both original evaluator result and FFI agree. -/
theorem canonical_global_entry_one_clock (input : Guest.InputBlob)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : evaluateHOLFiniteState {canonicalPanEntryState input with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (clock : initialized.clock = (canonicalPanEntryState input).clock)
    (fuel : Nat) (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState {initialized with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) = (result,post)) :
    ∃ final, evaluateHOLFiniteState {canonicalPanEntryState input with clock := fuel + 1}
      (.call none baselineCrepStart []) = (result,final) ∧ final.ffi = post.ffi :=
  pan_init_call_one_clock (canonicalPanEntryState input) initialized baselineCrepStart
    FrontendStages.Declarations.globalNewStart (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
    baselineRenamedMainBody [] .one (baseline_pan_generated_main input) (baseline_pan_renamed_main input)
    initialRun clock fuel result post run

#print axioms baseline_pan_generated_main
#print axioms baseline_pan_renamed_main
#print axioms canonical_global_entry_one_clock
end InitECandidate.Runtime

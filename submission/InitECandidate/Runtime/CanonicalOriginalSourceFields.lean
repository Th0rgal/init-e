import InitECandidate.Runtime.CanonicalOriginalSourceEntry
import InitECandidate.Runtime.PanSimpSourceFrame
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The actual original declaration evaluator installs the original code table. -/
theorem canonical_original_source_code (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).code = HolFiniteMapExact.empty.updateList
      (functionsHOL sourceDeclarations) := by
  classical
  exact evaluateDeclsHOLFinite_functions (sourceInitialState input) sourceDeclarations
    (canonicalOriginalSourceEntry input) (canonical_original_declarations_evaluate input)

/-- All original initialized runtime fields are explicit. Compiler-generated
memory/initialization choices occur only in the already identified exception table. -/
theorem canonical_original_source_fields (input : Guest.InputBlob) :
    canonicalOriginalSourceEntry input =
      {sourceInitialState input with
        globals := baselineGlobalNames.foldl
          (fun globals name => globals.update (name,.val (.word 0))) HolFiniteMapExact.empty
        eshapes := (canonicalPanEntryState input).eshapes
        code := HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)} := by
  have frame := pan_simp_source_frame (canonicalOriginalSourceEntry input)
    (canonicalUnrenamedSourceEntry input) (canonical_original_simplified_relation input)
  rw [canonical_unrenamed_source_fields,canonical_original_source_code] at frame
  exact frame

#print axioms canonical_original_source_code
#print axioms canonical_original_source_fields
end InitECandidate.Runtime

import InitECandidate.Runtime.CanonicalOriginalSourceFields
import InitECandidate.Runtime.ConstantMapUpdates
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Exact original global-map contents, including absence of undeclared names. -/
theorem canonical_original_globals_lookup (input : Guest.InputBlob) (name : MlS) :
    (canonicalOriginalSourceEntry input).globals.lookup name =
      if name ∈ baselineGlobalNames then some (.val (.word 0)) else none := by
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals)
    (canonical_original_source_fields input)
  have lookup := congrArg (fun map : HolFiniteMapExact MlS (ValueHOL 64) => map.lookup name) globals
  have updated := constant_updates_lookup (A := MlS) (B := ValueHOL 64) baselineGlobalNames
    HolFiniteMapExact.empty (.val (.word 0)) name
  exact lookup.trans updated

theorem canonical_original_ev_zero (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).globals.lookup (ofString "ev") = some (.val (.word 0)) := by
  rw [canonical_original_globals_lookup]
  have member : ofString "ev" ∈ baselineGlobalNames := by decide_cbv
  rw [if_pos member]

theorem canonical_original_continuation_zero (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).globals.lookup (ofString "cur_cont") = some (.val (.word 0)) := by
  rw [canonical_original_globals_lookup]
  have member : ofString "cur_cont" ∈ baselineGlobalNames := by decide_cbv
  rw [if_pos member]

theorem canonical_original_heap_pointer_zero (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).globals.lookup (ofString "heap_ptr") = some (.val (.word 0)) := by
  rw [canonical_original_globals_lookup]
  have member : ofString "heap_ptr" ∈ baselineGlobalNames := by decide_cbv
  rw [if_pos member]

#print axioms canonical_original_globals_lookup
#print axioms canonical_original_ev_zero
#print axioms canonical_original_continuation_zero
#print axioms canonical_original_heap_pointer_zero
end InitECandidate.Runtime

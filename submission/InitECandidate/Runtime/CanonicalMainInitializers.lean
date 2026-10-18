import InitECandidate.Runtime.MainAllInitializersCells
import InitECandidate.Runtime.CanonicalAlignedArena
import InitECandidate.Runtime.CanonicalOriginalGlobals
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000000

/-- The original challenge entry, with a supplied clock, reaches input
loading or terminates early within the complete initialization budget. -/
theorem canonical_main_initializers (input : Guest.InputBlob) (fuel : Nat)
    (budget : 1893 ≤ fuel) :
    let state := {canonicalOriginalSourceEntry input with clock := fuel}
    Reaches state (mainAt 0) (AllInitializerContinuation state) 1893 (mainAt 14) := by
  let state := {canonicalOriginalSourceEntry input with clock := fuel}
  have zero (name : MlS) (member : name ∈ baselineGlobalNames) :
      state.globals.lookup name = some (.val (.word 0)) := by
    change (canonicalOriginalSourceEntry input).globals.lookup name = _
    rw [canonical_original_globals_lookup, if_pos member]
  have words (names : List MlS)
      (included : names.all (fun name => decide (name ∈ baselineGlobalNames)) = true) :
      ∀ name ∈ names, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)) := by
    intro name member
    exact ⟨0, zero name (of_decide_eq_true (List.all_eq_true.mp included name member))⟩
  have entries (slots : List (MlS × BitVec 64))
      (included : slots.all (fun entry => decide (entry.1 ∈ baselineGlobalNames)) = true) :
      ∀ entry ∈ slots, ∃ word : BitVec 64, state.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    exact ⟨0, zero entry.1 (of_decide_eq_true (List.all_eq_true.mp included entry member))⟩
  apply evaluate_main_all_initializers_cells state 0 0 0 0 0 0 0 0 0
  case arena => exact canonical_original_aligned_arena input
  case code => exact canonical_original_source_code input
  case budget => exact budget
  case hashWords => exact entries _ (by decide_cbv)
  case sszWords => exact entries _ (by decide_cbv)
  case mptWords => exact entries _ (by decide_cbv)
  case rmdWords => exact entries _ (by decide_cbv)
  case forkWords => exact entries _ (by decide_cbv)
  case bnWords => exact words _ (by decide_cbv)
  case blsWords => exact words _ (by decide_cbv)
  case blakeWords => exact words _ (by decide_cbv)
  case b2Word => exact ⟨0, zero _ (by decide_cbv)⟩
  case expwWord => exact ⟨0, zero _ (by decide_cbv)⟩
  all_goals exact zero _ (by decide_cbv)

#print axioms canonical_main_initializers
end InitECandidate.Runtime

import InitECandidate.Runtime.RlpValidationWrapperCore
import InitECandidate.Runtime.RlpValidationHandledFrame
import InitECandidate.Runtime.RlpValidationNormalCleanupGlobals
import InitECandidate.Runtime.RlpValidationCleanupNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned wrapper-core execution restores its saved scratch mark and
retains the frame pointer through real handled validation and normal cleanup. -/
theorem rlpValidation_wrapper_core_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (mark : BitVec 64)
    (markLocal : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 3 ≤ state.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState state rlpValidationWrapperCore = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word mark)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  let called : ProgHOL 64 := .call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
    (ofString "_rlp_validate_items_body") arguments
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  rw [source_rlpValidation_wrapper_core] at run
  change evaluateHOLFiniteState state (.seq called rlpValidationNormalCleanup) = (some (.returned value),post) at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state called with
  | mk result next =>
    rw [callRun] at run
    cases result with
    | none =>
      have locals := evaluate_rlpValidation_handled_normal_locals state next arguments callRun
      have framePost := rlpValidation_handled_normal_frame state next arguments pointer length scratch frame ceiling inputLimit args
        noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) callRun
      have metadata := evaluateHOLFiniteState_metadata state called
      rw [callRun] at metadata
      have restored := rlpValidation_normal_cleanup_returned_globals next post mark value
        (by rw [locals]; exact markLocal) (metadata.1.trans code) run
      rw [restored]
      constructor
      · simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide] using framePost
    | some result =>
      have impossible := evaluate_rlpValidation_handled_no_return state arguments value
      change (evaluateHOLFiniteState state called).1 ≠ some (.returned value) at impossible
      rw [callRun] at impossible
      exact False.elim (impossible (Prod.mk.inj run).1)

#print axioms rlpValidation_wrapper_core_returned_globals
end InitECandidate.Runtime

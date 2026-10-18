import InitECandidate.Runtime.TxFixedBytesInputGlobals
import InitECandidate.Runtime.TxFixedBytesInputNamedGlobal
import InitECandidate.Runtime.RlpSliceInputArguments
import InitECandidate.Runtime.TxFixedBytesBodyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful extraction from the input-bounded slice prefix retains runtime globals. -/
theorem txFixedBytes_input_returned_global_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) = (some (.returned value),post)) :
    ∀ watched : MlS, post.globals.lookup watched = state.globals.lookup watched := by
  intro watched
  by_cases same : ofString "scratch_ptr" = watched
  · subst watched
    have kept := txFixedBytes_input_returned_globals state post array index input inputLength scratch frame filled ceiling inputLimit
      arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run
    exact kept.1.trans scratchGlobal.symm
  · exact txFixedBytes_input_returned_named_global state post watched same array index input inputLength scratch frame filled ceiling inputLimit
      arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run

#print axioms txFixedBytes_input_returned_global_frame
end InitECandidate.Runtime

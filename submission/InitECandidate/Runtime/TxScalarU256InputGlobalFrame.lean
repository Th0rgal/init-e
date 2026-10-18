import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.TxScalarU256InputNamedGlobal
import InitECandidate.Runtime.RlpSliceInputArguments
import InitECandidate.Runtime.TxScalarU256BodyGlobals
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The input-bounded prefix supplies the real scalar-u256 argument loads and
bounds every extraction by the common original input length. -/
theorem txScalarU256_input_returned_global_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index maximum input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (maxLocal : state.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_u256) = (some (.returned value),post)) :
    ∀ watched : MlS, post.globals.lookup watched = state.globals.lookup watched := by
  intro watched
  by_cases same : ofString "scratch_ptr" = watched
  · subst watched
    have kept := txScalarU256_input_returned_globals state post array index maximum input inputLength scratch frame count ceiling inputLimit
      arrayLocal indexLocal maxLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run
    exact kept.1.trans scratchGlobal.symm
  · exact txScalarU256_input_returned_named_global state post watched same array index maximum input inputLength scratch frame count ceiling inputLimit
      arrayLocal indexLocal maxLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run

#print axioms txScalarU256_input_returned_global_frame
end InitECandidate.Runtime

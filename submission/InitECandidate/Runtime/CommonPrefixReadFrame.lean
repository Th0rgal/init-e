import InitECandidate.Runtime.CommonPrefixBodyBound
import InitECandidate.Runtime.OriginalMinCode
import InitECandidate.Runtime.PanDecCallReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem min_readOnlyMemory : readOnlyMemory (sourceFunctionBody Guest.guestFn_min) = true := by
  rw [source_min_body]
  rfl

theorem commonPrefix_after_min_readOnly : readOnlyMemory commonPrefixAfterMin = true := by
  simp only [commonPrefixAfterMin,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Full original prefix comparison preserves memory and globals, including
min, byte-read errors, early returns and timeout at any fuel. -/
theorem evaluate_commonPrefix_body_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : BitVec 64)
    (leftLocal : state.locals.lookup (ofString "al") = some (.val (.word left)))
    (rightLocal : state.locals.lookup (ofString "bl") = some (.val (.word right)))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_common_prefix_length)).2.memory = state.memory ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_common_prefix_length)).2.globals = state.globals := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "al"),.var .local (ofString "bl")] = some [.val (.word left),.val (.word right)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,leftLocal,rightLocal]
  have installed : state.code.lookup (ofString "min") = some minCodeEntry := by
    rw [code]; exact originalRuntimeCode_min_lookup
  have lookup := lookup_source_min state.code.lookup left right installed
  rw [source_commonPrefix_body]
  exact evaluate_decCall_readOnly_frame state (ofString "n") (ofString "min") .one .one
    [.var .local (ofString "al"),.var .local (ofString "bl")] [.val (.word left),.val (.word right)]
    (sourceFunctionBody Guest.guestFn_min) commonPrefixAfterMin (minCalleeLocals left right) args lookup
    min_readOnlyMemory commonPrefix_after_min_readOnly

#print axioms min_readOnlyMemory
#print axioms commonPrefix_after_min_readOnly
#print axioms evaluate_commonPrefix_body_read_frame
end InitECandidate.Runtime

import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.PanDecCallReadFrame
import InitECandidate.Runtime.TrieWalkExtensionBranchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem trieWalk_extension_continuation_readOnly : readOnlyMemory trieWalkExtensionContinuation = true := by
  simp only [trieWalkExtensionContinuation,trieWalkExtensionComparison,trieWalkExtensionBranch,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual extension comparison and original position/node updates leave
memory and globals unchanged for all lengths, fuel and read outcomes. -/
theorem evaluate_trieWalk_extension_comparison_read_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F) (node nibs index size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state trieWalkExtensionComparison).2.memory = state.memory ∧
    (evaluateHOLFiniteState state trieWalkExtensionComparison).2.globals = state.globals := by
  rw [source_trieWalk_extension_comparison]
  rcases eval_trieWalk_comparison_arguments state (ofString "sl") node nibs index size
      nodeLocal nibsLocal posLocal sizeLocal with missing | ⟨left,args⟩
  · rw [evaluateHOLFiniteState_decCall_args_none state (ofString "eq2") .one (ofString "memeq") _ trieWalkExtensionContinuation missing]
    exact ⟨rfl,rfl⟩
  · let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "a",.val left)).update (ofString "b",.val (.word (nibs + index)))).update (ofString "n",.val (.word size))
    have installed : state.code.lookup (ofString "memeq") =
        some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
      rw [code]; exact originalRuntimeCode_memeq_lookup
    have lookup := pan_three_value_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
      (sourceFunctionBody Guest.guestFn_memeq) left (.word (nibs + index)) (.word size) (by decide) (by decide) (by decide) installed
    exact evaluate_decCall_readOnly_frame state (ofString "eq2") (ofString "memeq") .one .one
      (trieWalkComparisonArguments (ofString "sl")) [.val left,.val (.word (nibs + index)),.val (.word size)]
      (sourceFunctionBody Guest.guestFn_memeq) trieWalkExtensionContinuation callee args lookup
      memeq_readOnlyMemory trieWalk_extension_continuation_readOnly

/-- The extension length guard adds no memory or global writes. -/
theorem evaluate_trieWalk_extension_guard_read_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F) (node nibs index size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state trieWalkExtensionAfterLength).2.memory = state.memory ∧
    (evaluateHOLFiniteState state trieWalkExtensionAfterLength).2.globals = state.globals := by
  rw [source_trieWalk_extension_after_length,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  split
  · split
    · simp only [evaluateHOLFiniteState_skip]
      exact evaluate_trieWalk_extension_comparison_read_frame state node nibs index size nodeLocal nibsLocal posLocal sizeLocal code
    · simp [trieWalkEmptyReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite]
  · exact ⟨rfl,rfl⟩

#print axioms trieWalk_extension_continuation_readOnly
#print axioms evaluate_trieWalk_extension_comparison_read_frame
#print axioms evaluate_trieWalk_extension_guard_read_frame
end InitECandidate.Runtime

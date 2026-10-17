import InitECandidate.Runtime.TrieWalkExtensionChild
import InitECandidate.Runtime.PanDecCallNormalReadScope
import InitECandidate.Runtime.PanDecCallNormalScope
import InitECandidate.Runtime.MemeqReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The child selected after the real comparison is read from the original
pre-comparison memory; this follows from checked memeq purity and actual scope
restoration, rather than a hypothesis about the callee's memory effects. -/
theorem evaluate_trieWalk_extension_comparison_child {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state trieWalkExtensionComparison = (none,post)) :
    ∃ child : BitVec 64, state.memory (node + BitVec.ofNat 64 48) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) := by
  rw [source_trieWalk_extension_comparison] at run
  rcases eval_trieWalk_comparison_arguments state (ofString "sl") node nibs index size
      nodeLocal nibsLocal posLocal sizeLocal with missing | ⟨left,args⟩
  · rw [evaluateHOLFiniteState_decCall_args_none state (ofString "eq2") .one (ofString "memeq") _ trieWalkExtensionContinuation missing] at run
    cases run
  · let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "a",.val left)).update (ofString "b",.val (.word (nibs + index)))).update (ofString "n",.val (.word size))
    have installed : state.code.lookup (ofString "memeq") =
        some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
      rw [code]; exact originalRuntimeCode_memeq_lookup
    have lookup := pan_three_value_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
      (sourceFunctionBody Guest.guestFn_memeq) left (.word (nibs + index)) (.word size) (by decide) (by decide) (by decide) installed
    obtain ⟨value,ready,output,locals,memory,_,tail,restored⟩ := evaluate_decCall_normal_read_scope state post (ofString "eq2") (ofString "memeq") .one .one
      (trieWalkComparisonArguments (ofString "sl")) [.val left,.val (.word (nibs + index)),.val (.word size)]
      (sourceFunctionBody Guest.guestFn_memeq) trieWalkExtensionContinuation callee args lookup memeq_readOnlyMemory run
    let entered := setVarHOLFinite (ofString "eq2") value ready
    have kept : ∀ name, name ≠ ofString "eq2" → entered.locals.lookup name = state.locals.lookup name := by
      intro name different
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    obtain ⟨child,_,loaded,childLocal⟩ := evaluate_trieWalk_extension_continuation_child entered output node index size
      (by rw [kept _ (by decide)]; exact nodeLocal)
      (by rw [kept _ (by decide)]; exact posLocal) (by rw [kept _ (by decide)]; exact sizeLocal) tail
    refine ⟨child,?_,?_⟩
    · change ready.memory (node + BitVec.ofNat 64 48) = .word child at loaded
      rw [memory] at loaded
      exact loaded
    · rw [restored]
      exact (saved_local_lookup_other output.locals (ofString "eq2") (ofString "node") _ (by decide)).trans childLocal

#print axioms evaluate_trieWalk_extension_comparison_child
end InitECandidate.Runtime

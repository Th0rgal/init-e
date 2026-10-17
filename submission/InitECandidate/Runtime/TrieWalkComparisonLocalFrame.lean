import InitECandidate.Runtime.PanDecCallNormalLocalFrame
import InitECandidate.Runtime.TrieWalkExtensionAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original extension comparison preserves every caller local except
its two traversal updates and temporary comparison result. -/
theorem evaluate_trieWalk_extension_comparison_local_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index size : BitVec 64) (key : MlS)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (keyNode : key ≠ ofString "node") (keyPos : key ≠ ofString "pos") (keyResult : key ≠ ofString "eq2")
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state trieWalkExtensionComparison = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
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
    apply evaluate_decCall_normal_local_frame state post (ofString "eq2") (ofString "memeq") key .one .one
      (trieWalkComparisonArguments (ofString "sl")) [.val left,.val (.word (nibs + index)),.val (.word size)]
      (sourceFunctionBody Guest.guestFn_memeq) trieWalkExtensionContinuation callee keyResult args lookup ?_ run
    intro value ready output locals tail
    let entered := setVarHOLFinite (ofString "eq2") value ready
    have kept : ∀ name, name ≠ ofString "eq2" → entered.locals.lookup name = state.locals.lookup name := by
      intro name different
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    obtain ⟨_,frame,_,_,_⟩ := evaluate_trieWalk_extension_normal_position entered output index size
      ((kept _ (by decide)).trans posLocal) ((kept _ (by decide)).trans sizeLocal) tail
    exact frame key keyNode keyPos

#print axioms evaluate_trieWalk_extension_comparison_local_frame
end InitECandidate.Runtime

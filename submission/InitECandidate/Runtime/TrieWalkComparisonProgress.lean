import InitECandidate.Runtime.TrieWalkExtensionProgress
import InitECandidate.Runtime.PanDecCallNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the original extension comparison transports the
position/length update through the actual memeq call and local restoration.
No assumption about callee memory purity is used for these local facts. -/
theorem evaluate_trieWalk_extension_comparison_position {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index size length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state trieWalkExtensionComparison = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
    post.locals.lookup (ofString "nlen") = some (.val (.word length)) := by
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
    obtain ⟨value,ready,output,locals,tail,restored⟩ := evaluate_decCall_normal_scope state post (ofString "eq2") (ofString "memeq") .one .one
      (trieWalkComparisonArguments (ofString "sl")) [.val left,.val (.word (nibs + index)),.val (.word size)]
      (sourceFunctionBody Guest.guestFn_memeq) trieWalkExtensionContinuation callee args lookup run
    let entered := setVarHOLFinite (ofString "eq2") value ready
    have kept : ∀ name, name ≠ ofString "eq2" → entered.locals.lookup name = state.locals.lookup name := by
      intro name different
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    obtain ⟨advanced,frame,_,_,_⟩ := evaluate_trieWalk_extension_normal_position entered output index size
      (by rw [kept _ (by decide)]; exact posLocal) (by rw [kept _ (by decide)]; exact sizeLocal) tail
    rw [restored]
    constructor
    · exact (saved_local_lookup_other output.locals (ofString "eq2") (ofString "pos") _ (by decide)).trans advanced
    · exact (saved_local_lookup_other output.locals (ofString "eq2") (ofString "nlen") _ (by decide)).trans
        ((frame (ofString "nlen") (by decide) (by decide)).trans ((kept _ (by decide)).trans nlenLocal))

/-- Position-rank consequences for the original comparison, including scope
restoration. A positive accepted length decreases rank; zero does not. -/
theorem evaluate_trieWalk_extension_comparison_position_rank {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index size length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (within : index.toNat + size.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionComparison = (none,post)) :
    (index + size).toNat ≤ length.toNat ∧
    trieWalkPositionRank length post ≤ trieWalkPositionRank length state ∧
    (trieWalkPositionRank length post < trieWalkPositionRank length state ↔ 0 < size.toNat) := by
  obtain ⟨advanced,_⟩ := evaluate_trieWalk_extension_comparison_position state post node nibs index size length
    nodeLocal nibsLocal posLocal sizeLocal nlenLocal code run
  have nextNat : (index + size).toNat = index.toNat + size.toNat := by
    rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + size.toNat < 2 ^ 64; omega)]
  simp only [trieWalkPositionRank,advanced,posLocal]
  rw [nextNat]
  omega

#print axioms evaluate_trieWalk_extension_comparison_position
#print axioms evaluate_trieWalk_extension_comparison_position_rank
end InitECandidate.Runtime

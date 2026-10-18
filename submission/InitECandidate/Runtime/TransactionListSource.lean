import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionListArguments : List (ExpHOL 64) :=
  [.rfield 1 (.var .local (ofString "top")),.rfield 2 (.var .local (ofString "top"))]
def transactionListCallee (pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))

theorem source_transaction_list : transactionAt 12 =
    .decCall (ofString "lst") (.comb [.one,.one]) (ofString "rlp_list_to_slices") transactionListArguments (transactionAt 13) := by
  simp only [transactionListArguments,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_list_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tag pointer length total : BitVec 64)
    (topLocal : state.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)])) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) transactionListArguments =
      some [.val (.word pointer),.val (.word length)] := by
  simp [transactionListArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,topLocal]

theorem transaction_list_lookup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "rlp_list_to_slices") [.val (.word pointer),.val (.word length)] =
      some (sourceFunctionBody Guest.guestFn_rlp_list_to_slices,transactionListCallee pointer length,.comb [.one,.one]) := by
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  exact pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed

theorem transaction_list_normal_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tag pointer length total : BitVec 64)
    (topLocal : state.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (transactionAt 12) = (none,post)) :
    ∃ value bodyPost output,
      evaluateHOLFiniteState (callEntryStateHOLFinite state (transactionListCallee pointer length))
        (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),bodyPost) ∧
      (shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "lst") value {bodyPost with locals := state.locals})
        (transactionAt 13) = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "lst",state.locals.lookup (ofString "lst"))} := by
  rw [source_transaction_list] at run
  exact evaluate_decCall_checked_normal_exact_scope state post (ofString "lst") (ofString "rlp_list_to_slices")
    (.comb [.one,.one]) (.comb [.one,.one]) transactionListArguments _ _ (transactionAt 13) (transactionListCallee pointer length)
    (transaction_list_arguments state tag pointer length total topLocal) (transaction_list_lookup state pointer length code) run

#print axioms transaction_list_normal_scope
#print axioms source_transaction_list
#print axioms transaction_list_arguments
#print axioms transaction_list_lookup
end InitECandidate.Runtime

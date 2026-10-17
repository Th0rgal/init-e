import InitECandidate.Runtime.HashDeleteCountReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteFinalSwapStores : ProgHOL 64 :=
  .seq (.store (hashOrderAddress (ofString "order") (ofString "deleted_pos")) (.var .local (ofString "last_slot")))
    (.store (hashOrderAddress (ofString "order_pos") (ofString "last_slot")) (.var .local (ofString "deleted_pos")))

theorem source_hashDelete_final_swap_stores :
    (match hashDeleteCountTail with
     | .dec _ _ _ (.dec _ _ _ (.seq (.ite _ (.dec _ _ _ body) _) _)) => body
     | _ => .skip) = hashDeleteFinalSwapStores := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteFinalSwapStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

/-- Actual final swap updates forward and reverse order cells; locals and
clock are unchanged, including when both stores share an address. -/
theorem evaluate_hashDelete_final_swap_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos deletedPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_slot") = some (.val (.word lastSlot)))
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8)) :
    evaluateHOLFiniteState state hashDeleteFinalSwapStores =
      (none,sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
        (orderPos + lastSlot * 8) deletedPosition) := by
  have first := evaluate_store_word state (order + deletedPosition * 8) lastSlot
    (hashOrderAddress (ofString "order") (ofString "deleted_pos")) (.var .local (ofString "last_slot"))
    (eval_hashOrderAddress state _ _ order deletedPosition orderLocal deletedLocal) lastLocal orderDomain
  let written := sourceWriteWord state (order + deletedPosition * 8) lastSlot
  have second := evaluate_store_word written (orderPos + lastSlot * 8) deletedPosition
    (hashOrderAddress (ofString "order_pos") (ofString "last_slot")) (.var .local (ofString "deleted_pos"))
    (eval_hashOrderAddress written _ _ orderPos lastSlot reverseLocal lastLocal) deletedLocal reverseDomain
  unfold hashDeleteFinalSwapStores
  exact evaluate_seq_none first second

#print axioms source_hashDelete_final_swap_stores
#print axioms evaluate_hashDelete_final_swap_stores
end InitECandidate.Runtime

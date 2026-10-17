import InitECandidate.Runtime.HashDeleteFinalSwapStores
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteFinalSwapScope : ProgHOL 64 :=
  .dec (ofString "last_slot") .one (.load .one (hashOrderAddress (ofString "order") (ofString "last_pos"))) hashDeleteFinalSwapStores

theorem source_hashDelete_final_swap_scope :
    (match hashDeleteCountTail with
     | .dec _ _ _ (.dec _ _ _ (.seq (.ite _ swap _) _)) => swap
     | _ => .skip) = hashDeleteFinalSwapScope := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteFinalSwapScope hashDeleteFinalSwapStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

theorem evaluate_hashDelete_final_swap_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos deletedPosition lastPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (loadDomain : state.memaddrs (order + lastPosition * 8))
    (loadCell : state.memory (order + lastPosition * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8)) :
    evaluateHOLFiniteState state hashDeleteFinalSwapScope =
      (none,sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
        (orderPos + lastSlot * 8) deletedPosition) := by
  let entered := setVarHOLFinite (ofString "last_slot") (.val (.word lastSlot)) state
  have other : ∀ name, name ≠ ofString "last_slot" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have run := evaluate_hashDelete_final_swap_stores entered order orderPos deletedPosition lastSlot
    ((other _ (by decide)).trans orderLocal) ((other _ (by decide)).trans reverseLocal)
    ((other _ (by decide)).trans deletedLocal)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) orderDomain reverseDomain
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "order") (ofString "last_pos"))) = some (.val (.word lastSlot)) := by
    simp [hashOrderAddress,evalHOLExact,evalListHOLExact,orderLocal,lastLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact ⟨loadDomain,loadCell⟩
  unfold hashDeleteFinalSwapScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  dsimp only
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word lastSlot))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shape,run]
  dsimp only [sourceWriteWord,entered,setVarHOLFinite]
  rw [restore_updated_local]

#print axioms source_hashDelete_final_swap_scope
#print axioms evaluate_hashDelete_final_swap_scope
end InitECandidate.Runtime

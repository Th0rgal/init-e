import InitECandidate.Runtime.HashDeleteFinalSwapScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteFinalSwapCondition : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "deleted_pos")) (.var .local (ofString "last_pos"))

def hashDeleteFinalSwap : ProgHOL 64 := .ite hashDeleteFinalSwapCondition hashDeleteFinalSwapScope .skip

theorem source_hashDelete_final_swap :
    (match hashDeleteCountTail with
     | .dec _ _ _ (.dec _ _ _ (.seq swap _)) => swap
     | _ => .skip) = hashDeleteFinalSwap := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteFinalSwap hashDeleteFinalSwapCondition hashDeleteFinalSwapScope hashDeleteFinalSwapStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

theorem evaluate_hashDelete_final_swap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos deletedPosition lastPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (loadDomain : state.memaddrs (order + lastPosition * 8))
    (loadCell : state.memory (order + lastPosition * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8)) :
    evaluateHOLFiniteState state hashDeleteFinalSwap =
      (none,if deletedPosition = lastPosition then state else
        sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
          (orderPos + lastSlot * 8) deletedPosition) := by
  classical
  have run := evaluate_hashDelete_final_swap_scope state order orderPos deletedPosition lastPosition lastSlot
    orderLocal reverseLocal deletedLocal lastLocal loadDomain loadCell orderDomain reverseDomain
  unfold hashDeleteFinalSwap
  rw [evaluateHOLFiniteState_ite]
  by_cases same : deletedPosition = lastPosition
  · simp [hashDeleteFinalSwapCondition,evalHOLExact,deletedLocal,lastLocal,
      Compiler.Encoders.Asm.wordCmpHOL,same,evaluateHOLFiniteState_skip]
  · simp [hashDeleteFinalSwapCondition,evalHOLExact,deletedLocal,lastLocal,
      Compiler.Encoders.Asm.wordCmpHOL,same,run]

def hashDeleteFinalStores : ProgHOL 64 := .seq hashDeleteFinalSwap hashDeleteCountReturn

theorem source_hashDelete_final_stores :
    (match hashDeleteCountTail with | .dec _ _ _ (.dec _ _ _ body) => body | _ => .skip) = hashDeleteFinalStores := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteFinalStores hashDeleteFinalSwap hashDeleteFinalSwapCondition hashDeleteFinalSwapScope hashDeleteFinalSwapStores hashDeleteCountReturn
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

#print axioms source_hashDelete_final_stores

#print axioms source_hashDelete_final_swap
#print axioms evaluate_hashDelete_final_swap
end InitECandidate.Runtime

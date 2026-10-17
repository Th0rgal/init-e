import InitECandidate.Runtime.HashDeleteFinalSwap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_final_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition lastPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (loadDomain : state.memaddrs (order + lastPosition * 8))
    (loadCell : state.memory (order + lastPosition * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countDomain : state.memaddrs (table + 24)) :
    let swapped := if deletedPosition = lastPosition then state else
      sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
    evaluateHOLFiniteState state hashDeleteFinalStores =
      (some (.returned (.val (.word (1 : BitVec 64)))),emptyLocalsHOLFinite (sourceWriteWord swapped (table + 24) lastPosition)) := by
  classical
  dsimp only
  let swapped := if deletedPosition = lastPosition then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have swap := evaluate_hashDelete_final_swap state order orderPos deletedPosition lastPosition lastSlot
    orderLocal reverseLocal deletedLocal lastLocal loadDomain loadCell orderDomain reverseDomain
  have locals : swapped.locals = state.locals := by unfold swapped; split <;> rfl
  have domain : swapped.memaddrs = state.memaddrs := by unfold swapped; split <;> rfl
  have returned := evaluate_hashDelete_count_return swapped table lastPosition
    (by rw [locals]; exact tableLocal) (by rw [locals]; exact lastLocal) (by rw [domain]; exact countDomain)
  unfold hashDeleteFinalStores
  exact evaluate_seq_none swap returned

#print axioms evaluate_hashDelete_final_stores
end InitECandidate.Runtime

import InitECandidate.Runtime.HashDeleteFinalStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

theorem source_hashDelete_count_tail : hashDeleteCountTail =
    .dec (ofString "n") .one (.load .one (hashLocalAddress (ofString "t") 24))
      (.dec (ofString "last_pos") .one (.op .sub [.var .local (ofString "n"),.const 1]) hashDeleteFinalStores) := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteFinalStores hashDeleteFinalSwap hashDeleteFinalSwapCondition hashDeleteFinalSwapScope hashDeleteFinalSwapStores hashDeleteCountReturn
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

theorem evaluate_hashDelete_count_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (countDomain : state.memaddrs (table + 24))
    (countCell : state.memory (table + 24) = .word count)
    (loadDomain : state.memaddrs (order + (count - 1) * 8))
    (loadCell : state.memory (order + (count - 1) * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8)) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let loaded := setVarHOLFinite (ofString "n") (.val (.word count)) state
  let entered := setVarHOLFinite (ofString "last_pos") (.val (.word (count - 1))) loaded
  have other : ∀ name, name ≠ ofString "n" → name ≠ ofString "last_pos" → entered.locals.lookup name = state.locals.lookup name := by
    intro name notN notLast
    simp [entered,loaded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notN,Ne.symm notLast]
  have lastLocal : entered.locals.lookup (ofString "last_pos") = some (.val (.word (count - 1))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have run := evaluate_hashDelete_final_stores entered table order orderPos deletedPosition (count - 1) lastSlot
    ((other _ (by decide) (by decide)).trans orderLocal) ((other _ (by decide) (by decide)).trans reverseLocal)
    ((other _ (by decide) (by decide)).trans deletedLocal) lastLocal loadDomain loadCell orderDomain reverseDomain
    ((other _ (by decide) (by decide)).trans tableLocal) countDomain
  have initial : @evalHOLExact 64 F _ loaded.toExact
      (fun address => Classical.propDecidable (loaded.memaddrs address))
      (.op .sub [.var .local (ofString "n"),.const 1]) = some (.val (.word (count - 1))) := by
    simp [loaded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_hashDelete_count_tail,evaluate_header_load_scope state (ofString "n") (ofString "t") table 24 count _ tableLocal countDomain countCell]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word (count - 1)))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shape,run]
  dsimp only
  split <;> exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms source_hashDelete_count_tail
#print axioms evaluate_hashDelete_count_tail
end InitECandidate.Runtime

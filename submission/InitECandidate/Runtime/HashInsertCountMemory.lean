import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact bookkeeping memory effects and preservation of every separate word. -/
theorem evaluate_hashInsert_count_tail_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos count index : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (countMemory : state.memory (table + 24) = .word count) :
    ∃ post, evaluateHOLFiniteState state hashInsertCountTail = (some (.returned (.val (.word 0))),post) ∧
      post.memory = (sourceWriteWord (sourceWriteWord (sourceWriteWord state
        (order + count * 8) index) (orderPos + index * 8) count) (table + 24) (count + 1)).memory ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, watched ≠ order + count * 8 → watched ≠ orderPos + index * 8 →
        watched ≠ table + 24 → post.memory watched = state.memory watched := by
  classical
  let entered := setVarHOLFinite (ofString "n") (.val (.word count)) state
  let bodyPost := emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord
    (sourceWriteWord entered (order + count * 8) index) (orderPos + index * 8) count) (table + 24) (count + 1))
  let post := {bodyPost with locals := (HolFiniteMapExact.resVarEq bodyPost.locals
    (ofString "n",state.locals.lookup (ofString "n")))}
  have lookup (name : MlS) (different : ofString "n" ≠ name) : entered.locals.lookup name = state.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have countLocal : entered.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_hashInsert_count_stores entered table order orderPos count index
    ((lookup _ (by decide)).trans tableLocal) ((lookup _ (by decide)).trans orderLocal)
    ((lookup _ (by decide)).trans orderPosLocal) countLocal ((lookup _ (by decide)).trans indexLocal)
    orderDomain orderPosDomain countDomain
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "t") 24)) = some (.val (.word count)) := by
    simp [evalHOLExact,hashLocalAddress,evalListHOLExact,tableLocal,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact ⟨countDomain,countMemory⟩
  refine ⟨post,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · unfold hashInsertCountTail
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [loaded]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word count))) = true := by
      simp [shapeEqHOL,shapeOfHOLExact]
    dsimp only
    rw [if_pos shapeOk,body]
  · intro watched first second third
    change (sourceWriteWord (sourceWriteWord (sourceWriteWord state
      (order + count * 8) index) (orderPos + index * 8) count) (table + 24) (count + 1)).memory watched = _
    simp only [sourceWriteWord]
    rw [if_neg third,if_neg second,if_neg first]

#print axioms evaluate_hashInsert_count_tail_memory
end InitECandidate.Runtime

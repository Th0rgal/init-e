import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_count_tail_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      post.memory (table + 24) = .word (count + 1) ∧ post.clock = state.clock ∧
      post.memory = (sourceWriteWord (sourceWriteWord (sourceWriteWord state
        (order + count * 8) index) (orderPos + index * 8) count) (table + 24) (count + 1)).memory ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ capacity used : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
          panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
          panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧
          panByteAlignHOL (used + slot) ≠ table + 24) →
        hashOccupiedCount capacity (hashOccupancyRead post used) =
          hashOccupiedCount capacity (hashOccupancyRead state used) := by
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
  refine ⟨post,?_,?_,rfl,rfl,rfl,rfl,?_⟩
  · unfold hashInsertCountTail
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [loaded]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word count))) = true := by
      simp [shapeEqHOL,shapeOfHOLExact]
    dsimp only
    rw [if_pos shapeOk,body]
  · simp [post,bodyPost,emptyLocalsHOLFinite,sourceWriteWord]
  · intro capacity used separate
    let first := sourceWriteWord entered (order + count * 8) index
    let second := sourceWriteWord first (orderPos + index * 8) count
    have one := sourceWriteWord_occupancy_preserved entered capacity used (order + count * 8) index
      (fun slot bound => (separate slot bound).1)
    have two := sourceWriteWord_occupancy_preserved first capacity used (orderPos + index * 8) count
      (fun slot bound => (separate slot bound).2.1)
    have three := sourceWriteWord_occupancy_preserved second capacity used (table + 24) (count + 1)
      (fun slot bound => (separate slot bound).2.2)
    exact three.trans (two.trans one)

#print axioms evaluate_hashInsert_count_tail_frame
end InitECandidate.Runtime

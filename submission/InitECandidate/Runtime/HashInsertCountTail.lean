import InitECandidate.Runtime.HashProbeSource
import InitECandidate.Runtime.HashOccupancyPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def sourceFindLocalScope (name : MlS) : ProgHOL 64 → Option (ProgHOL 64)
  | .dec binder shape value body =>
      if binder == name then some (.dec binder shape value body) else sourceFindLocalScope name body
  | .decCall _ _ _ _ body => sourceFindLocalScope name body
  | .seq first rest => (sourceFindLocalScope name first).orElse (fun _ => sourceFindLocalScope name rest)
  | _ => none

def hashLocalAddress (name : MlS) (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .local name,.const offset]

def hashOrderAddress (name index : MlS) : ExpHOL 64 :=
  .op .add [.var .local name,.panop .mul [.var .local index,.const 8]]

def hashInsertCountStores : ProgHOL 64 :=
  .seq (.store (hashOrderAddress (ofString "order") (ofString "n")) (.var .local (ofString "i")))
    (.seq (.store (hashOrderAddress (ofString "order_pos") (ofString "i")) (.var .local (ofString "n")))
      (.seq (.store (hashLocalAddress (ofString "t") 24) (.op .add [.var .local (ofString "n"),.const 1]))
        (.return (.const 0))))

def hashInsertCountTail : ProgHOL 64 :=
  .dec (ofString "n") .one (.load .one (hashLocalAddress (ofString "t") 24)) hashInsertCountStores

/-- The count/order update tail is a literal scope of the immutable source. -/
theorem source_htabInsert_count_tail :
    sourceFindLocalScope (ofString "n") (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some hashInsertCountTail := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_insert_raw,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,sourceFindLocalScope,Option.orElse,
    hashInsertCountTail,hashInsertCountStores,hashLocalAddress,hashOrderAddress]
  rfl

theorem eval_hashLocalAddress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer offset : BitVec 64)
    (binding : state.locals.lookup name = some (.val (.word pointer))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashLocalAddress name offset) =
        some (.val (.word (pointer + offset))) := by
  simp [hashLocalAddress,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem eval_hashOrderAddress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name indexName : MlS) (pointer index : BitVec 64)
    (pointerLocal : state.locals.lookup name = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup indexName = some (.val (.word index))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashOrderAddress name indexName) =
        some (.val (.word (pointer + index * 8))) := by
  simp [hashOrderAddress,evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

/-- Actual count-tail stores update order, inverse order and item count.
    The complete post-state records all memory effects at zero source clocks. -/
theorem evaluate_hashInsert_count_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos count index : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (countLocal : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24)) :
    evaluateHOLFiniteState state hashInsertCountStores =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite
        (sourceWriteWord (sourceWriteWord (sourceWriteWord state (order + count * 8) index)
          (orderPos + index * 8) count) (table + 24) (count + 1))) := by
  let first := sourceWriteWord state (order + count * 8) index
  let second := sourceWriteWord first (orderPos + index * 8) count
  let third := sourceWriteWord second (table + 24) (count + 1)
  have one := evaluate_store_word state (order + count * 8) index _ (.var .local (ofString "i"))
    (eval_hashOrderAddress state (ofString "order") (ofString "n") order count orderLocal countLocal)
    indexLocal orderDomain
  have two := evaluate_store_word first (orderPos + index * 8) count _ (.var .local (ofString "n"))
    (eval_hashOrderAddress first (ofString "order_pos") (ofString "i") orderPos index orderPosLocal indexLocal)
    countLocal orderPosDomain
  have plus : @evalHOLExact 64 F _ second.toExact
      (fun address => Classical.propDecidable (second.memaddrs address))
      (.op .add [.var .local (ofString "n"),.const 1]) = some (.val (.word (count + 1))) := by
    simp [evalHOLExact,evalListHOLExact,countLocal,wordOpHOL,wordOp,valueIsWord,valueWord,second,first,sourceWriteWord]
  have three := evaluate_store_word second (table + 24) (count + 1) _ _
    (eval_hashLocalAddress second (ofString "t") table 24 tableLocal) plus countDomain
  have returned : evaluateHOLFiniteState third (.return (.const 0)) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite third) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  exact evaluate_seq_none one (evaluate_seq_none two (evaluate_seq_none three returned))

/-- Include the actual header read and scoped n declaration around the
bookkeeping stores. The returned header count is the word successor. -/
theorem evaluate_hashInsert_count_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  refine ⟨post,?_,?_,rfl,?_⟩
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

#print axioms evaluate_hashInsert_count_tail
#print axioms source_htabInsert_count_tail
#print axioms eval_hashOrderAddress
#print axioms evaluate_hashInsert_count_stores
end InitECandidate.Runtime

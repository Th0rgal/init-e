import InitECandidate.Runtime.RlpUncheckedSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original unchecked long-string branch spends only the length
reader's ticks; its local declaration and final return add none. -/
theorem evaluate_rlpUnchecked_long_string_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (ticks : (header - 183).toNat + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongString
    state.clock ≤ evaluated.2.clock + ((header - 183).toNat + 2) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] =
      some [.val (.word (pointer + 1)),.val (.word (header - 183))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  have bound := evaluate_rlpReadLength_straight_declaration_bounded entered (ofString "n")
    (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")])) (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
    (pointer + 1) (header - 183) args code ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_string,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered (.decCall (ofString "n") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
      (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]))); _) ∧ _
  cases run : evaluateHOLFiniteState entered (.decCall (ofString "n") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
      (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]))) with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpUnchecked_long_string_bounded
/-- The original unchecked long-list branch spends only the length
reader's ticks; its local declaration and final return add none. -/
theorem evaluate_rlpUnchecked_long_list_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (ticks : (header - 247).toNat + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongList
    state.clock ≤ evaluated.2.clock + ((header - 247).toNat + 2) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll2" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll2") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")] =
      some [.val (.word (pointer + 1)),.val (.word (header - 247))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  have bound := evaluate_rlpReadLength_straight_declaration_bounded entered (ofString "n2")
    (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")])) (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
    (pointer + 1) (header - 247) args code ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_list,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered (.decCall (ofString "n2") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
      (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")]))); _) ∧ _
  cases run : evaluateHOLFiniteState entered (.decCall (ofString "n2") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
      (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")]))) with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpUnchecked_long_list_bounded
theorem evaluate_rlpUnchecked_long_string_fixed_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongString
    state.clock ≤ evaluated.2.clock + (10) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have small : (header - 183).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 183 ≤ header.toNat; omega)]
    change header.toNat - 183 ≤ 8
    omega
  have bound := evaluate_rlpUnchecked_long_string_bounded state pointer header pointerLocal headerLocal code (by omega)
  dsimp only at bound ⊢
  exact ⟨by omega,bound.2⟩

#print axioms evaluate_rlpUnchecked_long_string_fixed_bounded
theorem evaluate_rlpUnchecked_long_list_fixed_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongList
    state.clock ≤ evaluated.2.clock + (10) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have small : (header - 247).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ header.toNat; omega)]
    change header.toNat - 247 ≤ 8
    omega
  have bound := evaluate_rlpUnchecked_long_list_bounded state pointer header pointerLocal headerLocal code (by omega)
  dsimp only at bound ⊢
  exact ⟨by omega,bound.2⟩

#print axioms evaluate_rlpUnchecked_long_list_fixed_bounded
end InitECandidate.Runtime

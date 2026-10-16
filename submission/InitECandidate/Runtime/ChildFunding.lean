import InitECandidate.Runtime.FrameHalt

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def childLoad (offset : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "child"), .const offset])
def childSum (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [fundingLoad offset, childLoad offset]
theorem source_childError_body : sourceFunctionBody Guest.guestFn_incorporate_child_on_error =
    .seq (.store (fundingAddress 64) (childSum 64))
      (.seq (.store (fundingAddress 72) (childSum 72))
        (.seq (.store (fundingAddress 184) (childSum 184)) (.return (.const 0)))) := by cbv

theorem eval_childSum {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (parent child offset pv cv : BitVec 64)
    (hp : state.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (hc : state.locals.lookup (ofString "child") = some (.val (.word child)))
    (dp : state.memaddrs (parent + offset)) (dc : state.memaddrs (child + offset))
    (mp : state.memory (parent + offset) = .word pv)
    (mc : state.memory (child + offset) = .word cv) :
    @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (childSum offset) =
      some (.val (.word (pv + cv))) := by
  classical
  unfold childSum
  simp only [evalHOLExact, evalListHOLExact]
  rw [eval_fundingLoad state parent offset pv hp dp mp]
  simp [childLoad, evalHOLExact, evalListHOLExact, toExact, hc, wordOpHOL, wordOp,
    valueIsWord, valueWord, isWfShapeExactHOL, memLoadHOLExact, dc, mc]

/-- Error incorporation drops the child's spill liability; it cannot increase
combined regular funding. -/
def GasFunding.mergeError (parent child : GasFunding) : GasFunding :=
  ⟨parent.left + child.left, parent.used + child.used, parent.spilled⟩
theorem GasFunding.mergeError_potential (parent child : GasFunding)
    (budget : parent.potential + child.potential ≤ 200000000) :
    (parent.mergeError child).potential + child.spilled.toNat =
      parent.potential + child.potential := by
  have lb : parent.left.toNat + child.left.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget; omega
  have ub : parent.used.toNat + child.used.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget; omega
  simp only [GasFunding.mergeError, GasFunding.potential, BitVec.toNat_add,
    Nat.mod_eq_of_lt lb, Nat.mod_eq_of_lt ub]
  omega

noncomputable def childErrorPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (parent pl cl ps cs pu cu : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord
    (sourceWriteWord state (parent + 64) (pl + cl)) (parent + 72) (ps + cs))
    (parent + 184) (pu + cu))

theorem evaluate_childError {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (parent child pl cl ps cs pu cu : BitVec 64)
    (hp : state.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (hc : state.locals.lookup (ofString "child") = some (.val (.word child)))
    (dp : ∀ o ∈ ([64,72,184] : List (BitVec 64)), state.memaddrs (parent + o))
    (dc : ∀ o ∈ ([64,72,184] : List (BitVec 64)), state.memaddrs (child + o))
    (mpl : state.memory (parent + 64) = .word pl)
    (mcl : state.memory (child + 64) = .word cl)
    (mps : state.memory (parent + 72) = .word ps)
    (mcs : state.memory (child + 72) = .word cs)
    (mpu : state.memory (parent + 184) = .word pu)
    (mcu : state.memory (child + 184) = .word cu)
    (sep72 : child + 72 ≠ parent + 64)
    (sep184a : child + 184 ≠ parent + 64)
    (sep184b : child + 184 ≠ parent + 72) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_incorporate_child_on_error) =
      (some (.returned (.val (.word 0))), childErrorPost state parent pl cl ps cs pu cu) := by
  classical
  let one := sourceWriteWord state (parent + 64) (pl + cl)
  let two := sourceWriteWord one (parent + 72) (ps + cs)
  let three := sourceWriteWord two (parent + 184) (pu + cu)
  have first : evaluateHOLFiniteState state (.store (fundingAddress 64) (childSum 64)) =
      (none, one) := evaluate_store_word state _ _ _ _ (eval_fundingAddress state parent 64 hp)
        (eval_childSum state parent child 64 pl cl hp hc (dp 64 (by simp))
          (dc 64 (by simp)) mpl mcl) (dp 64 (by simp))
  have p72 : one.memory (parent + 72) = .word ps := by
    simpa [one, sourceWriteWord] using mps
  have c72 : one.memory (child + 72) = .word cs := by
    change (if child + 72 = parent + 64 then _ else _) = _
    rw [if_neg sep72]; exact mcs
  have second : evaluateHOLFiniteState one (.store (fundingAddress 72) (childSum 72)) =
      (none, two) := evaluate_store_word one _ _ _ _ (eval_fundingAddress one parent 72 hp)
        (eval_childSum one parent child 72 ps cs hp hc (dp 72 (by simp))
          (dc 72 (by simp)) p72 c72) (dp 72 (by simp))
  have p184 : two.memory (parent + 184) = .word pu := by
    simpa [two, one, sourceWriteWord] using mpu
  have c184 : two.memory (child + 184) = .word cu := by
    change (if child + 184 = parent + 72 then _ else
      if child + 184 = parent + 64 then _ else _) = _
    rw [if_neg sep184b, if_neg sep184a]; exact mcu
  have third : evaluateHOLFiniteState two (.store (fundingAddress 184) (childSum 184)) =
      (none, three) := evaluate_store_word two _ _ _ _ (eval_fundingAddress two parent 184 hp)
        (eval_childSum two parent child 184 pu cu hp hc (dp 184 (by simp))
          (dc 184 (by simp)) p184 c184) (dp 184 (by simp))
  have finish : evaluateHOLFiniteState three (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite three) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  rw [source_childError_body]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third finish))

theorem childErrorPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (parent ps cs : BitVec 64) (p c : GasFunding)
    (memory : HasGasFunding state parent p) :
    HasGasFunding (childErrorPost state parent p.left c.left ps cs p.used c.used)
      parent (p.mergeError c) := by
  unfold HasGasFunding
  simp [childErrorPost, sourceWriteWord, emptyLocalsHOLFinite, GasFunding.mergeError]
  exact memory.2.2

/-- The actual ordered stores have the funding bound needed when popping a
failed child, and preserve clock. Execution itself is established above. -/
theorem childErrorPost_bound {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (parent ps cs : BitVec 64) (p c : GasFunding)
    (memory : HasGasFunding state parent p)
    (budget : p.potential + c.potential ≤ 200000000) :
    HasGasFunding (childErrorPost state parent p.left c.left ps cs p.used c.used)
      parent (p.mergeError c) ∧
    (p.mergeError c).potential ≤ 200000000 ∧
    (childErrorPost state parent p.left c.left ps cs p.used c.used).clock = state.clock := by
  refine ⟨childErrorPost_funding state parent ps cs p c memory, ?_, rfl⟩
  have conserved := p.mergeError_potential c budget
  omega

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_childError

#print axioms InitECandidate.Runtime.childErrorPost_bound

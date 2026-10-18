import InitECandidate.Runtime.U256FromBeLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initializing the four limbs and index and returning the result adds no
source clocks to the checked byte-loop bound. -/
theorem evaluate_u256FromBe_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (budget : length.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state u256FromBeInitialized
    state.clock ≤ evaluated.2.clock + length.toNat ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let initial := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "l3") (.val (.word (0 : BitVec 64)))
      (setVarHOLFinite (ofString "l2") (.val (.word (0 : BitVec 64)))
        (setVarHOLFinite (ofString "l1") (.val (.word (0 : BitVec 64)))
          (setVarHOLFinite (ofString "l0") (.val (.word (0 : BitVec 64))) state))))
  have atLength : initial.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "n" by decide,show ofString "l0" ≠ ofString "n" by decide,
      show ofString "l1" ≠ ofString "n" by decide,show ofString "l2" ≠ ofString "n" by decide,
      show ofString "l3" ≠ ofString "n" by decide] using lengthLocal
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_u256FromBe_loop_bounded initial 0 length
    atIndex atLength (by simp) (by change length.toNat - (0 : BitVec 64).toNat ≤ state.clock; simpa using budget)
  let returned : ProgHOL 64 := .return (.rstruct [.var .local (ofString "l0"),
    .var .local (ofString "l1"),.var .local (ofString "l2"),.var .local (ofString "l3")])
  have bound := evaluate_sequence_straight_bounded initial u256FromBeLoop returned length.toNat
    (by rw [run]; exact ⟨by simpa using cost,remaining,noTimeout⟩) (by rfl)
  have terminal := evaluate_seq_terminal initial u256FromBeLoop returned
    (fun current => evaluate_return_terminal current _)
  dsimp only [returned] at bound terminal
  rw [← source_u256FromBe_loop_and_return] at bound terminal
  rw [source_u256FromBe_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases actual : evaluateHOLFiniteState initial u256FromBeLoopAndReturn with
  | mk result output =>
    rw [actual] at bound terminal
    exact ⟨bound.1,bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_u256FromBe_initialized_bounded
end InitECandidate.Runtime

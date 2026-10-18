import InitECandidate.Runtime.TxScalarWordLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual scalar-word conversion, after its size guard, costs at most
eight source clocks including failed reads and the final return. -/
theorem evaluate_txScalarWord_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (fieldLocal : state.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (small : length.toNat ≤ 8) (budget : 8 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state txScalarWordInitialized
    state.clock ≤ evaluated.2.clock + 8 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let initial := setVarHOLFinite (ofString "j") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "v") (.val (.word (0 : BitVec 64))) state)
  have atField : initial.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "j" ≠ ofString "f" by decide,show ofString "v" ≠ ofString "f" by decide] using fieldLocal
  have atIndex : initial.locals.lookup (ofString "j") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atValue : initial.locals.lookup (ofString "v") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "v" by decide]
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_txScalarWord_loop_bounded initial pointer 0 length 0
    atIndex atField atValue (by simp) (by change length.toNat - 0 ≤ state.clock; omega)
  have bound := evaluate_sequence_straight_bounded initial txScalarWordLoop (.return (.var .local (ofString "v")))
    length.toNat (by rw [run]; exact ⟨by simpa using cost,remaining,noTimeout⟩) (by decide)
  have terminal := evaluate_seq_terminal initial txScalarWordLoop (.return (.var .local (ofString "v")))
    (fun current => evaluate_return_terminal current _)
  rw [← source_txScalarWord_loop_and_return] at bound terminal
  rw [source_txScalarWord_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases actual : evaluateHOLFiniteState initial txScalarWordLoopAndReturn with
  | mk result output =>
    rw [actual] at bound terminal
    exact ⟨Nat.le_trans bound.1 (Nat.add_le_add_left small _),bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_txScalarWord_initialized_bounded
end InitECandidate.Runtime

import InitECandidate.Runtime.RlpReadLengthLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original local declarations, the byte-reading loop and its return
use at most n source ticks and return a word whenever they return normally. -/
theorem evaluate_rlpReadLength_after_check_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpReadLengthAfterCheck = (result,post) ∧
      state.clock ≤ post.clock + length.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ word : BitVec 64, value = .val (.word word)) := by
  let withValue := setVarHOLFinite (ofString "v") (.val (.word (0 : BitVec 64))) state
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) withValue
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atValue : entered.locals.lookup (ofString "v") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,withValue,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "v" by decide]
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,withValue,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "p" by decide,show ofString "v" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [entered,withValue,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "n" by decide,show ofString "v" ≠ ofString "n" by decide] using lengthLocal
  obtain ⟨result,middle,loop,cost,remaining,noTimeout,done,noReturn⟩ :=
    evaluate_rlpReadLength_loop_bounded entered pointer 0 length 0 atIndex atLength atPointer atValue (Nat.zero_le _)
      (by change length.toNat - 0 ≤ state.clock; omega)
  have sequence : ∃ result post,
      evaluateHOLFiniteState entered (.seq rlpReadLengthLoop (.return (.var .local (ofString "v")))) = (result,post) ∧
      state.clock ≤ post.clock + length.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ word : BitVec 64, value = .val (.word word)) := by
    rw [evaluateHOLFiniteState_seq_line780,loop]
    cases result with
    | none =>
      obtain ⟨word,atWord⟩ := (done rfl).2.2.2
      have finish : evaluateHOLFiniteState middle (.return (.var .local (ofString "v"))) =
          (some (.returned (.val (.word word))),emptyLocalsHOLFinite middle) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,atWord,shapeOfHOLExact]
      dsimp only
      rw [finish]
      refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
      intro value equal
      exact ⟨word,by simpa using equal.symm⟩
    | some stopped =>
      refine ⟨_,_,rfl,cost,remaining,noTimeout,?_⟩
      intro value returned
      exact False.elim (noReturn value returned)
  obtain ⟨result,output,sequenceRun,total,remaining,noTimeout,returned⟩ := sequence
  let restoredI := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "i",withValue.locals.lookup (ofString "i"))}
  have iRun : evaluateHOLFiniteState withValue (.dec (ofString "i") .one (.const 0)
      (.seq rlpReadLengthLoop (.return (.var .local (ofString "v"))))) = (result,restoredI) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered (.seq rlpReadLengthLoop (.return (.var .local (ofString "v")))); _) = _
    rw [sequenceRun]
  let final := {restoredI with locals := HolFiniteMapExact.resVarEq restoredI.locals (ofString "v",state.locals.lookup (ofString "v"))}
  refine ⟨result,final,?_,total,remaining,noTimeout,returned⟩
  rw [source_rlpReadLength_after_check,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState withValue (.dec (ofString "i") .one (.const 0)
    (.seq rlpReadLengthLoop (.return (.var .local (ofString "v"))))); _) = _
  rw [iRun]

#print axioms evaluate_rlpReadLength_after_check_bounded
end InitECandidate.Runtime

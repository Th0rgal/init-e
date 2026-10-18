import InitECandidate.Runtime.TxScalarWordStep
import InitECandidate.Runtime.RankedLoopReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txScalarWordRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "j") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

/-- The actual length-reader loop costs at most one tick per remaining byte,
including failed reads; all successful steps advance the source index. -/
theorem evaluate_txScalarWord_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer index length value : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (fieldLocal : state.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (bounded : index.toNat ≤ length.toNat) (ticks : length.toNat - index.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state txScalarWordLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "j") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) ∧
        ∃ value : BitVec 64, post.locals.lookup (ofString "v") = some (.val (.word value))) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    (∃ index : BitVec 64, current.locals.lookup (ofString "j") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
    current.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) ∧
    ∃ value : BitVec 64, current.locals.lookup (ofString "v") = some (.val (.word value))
  let returnedProperty := fun _ : ValueHOL 64 => False
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "f")))) =
      some (.val (.word (if txScalarWordRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atField,⟨value,atValue⟩⟩
    have rankEq : txScalarWordRank length current = length.toNat - index.toNat := by simp [txScalarWordRank,atIndex]
    by_cases inside : index.toNat < length.toNat
    · have nonzero : txScalarWordRank length current ≠ 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atField,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,nonzero]
    · have zero : txScalarWordRank length current = 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atField,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by intro current valid; exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F,
      txScalarWordRank length (decClockHOLFinite current) = txScalarWordRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < txScalarWordRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current txScalarWordStep = (none,post) ∧ invariant post ∧
          txScalarWordRank length post < txScalarWordRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current txScalarWordStep = (some result,post) ∧
           (∀ value, result = .returned value → returnedProperty value))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atField,⟨value,atValue⟩⟩ positive _
    have rankEq : txScalarWordRank length current = length.toNat - index.toNat := by simp [txScalarWordRank,atIndex]
    have inside : index.toNat < length.toNat := by rw [rankEq] at positive; omega
    rcases evaluate_txScalarWord_step_cases current pointer length index value atField atIndex atValue with failed | advanced
    · exact ⟨current,by omega,by omega,Or.inr ⟨.error,by simp,by simp,by simp,failed,by intro value impossible; cases impossible⟩⟩
    · obtain ⟨nextValue,advanced⟩ := advanced
      let post := setVarHOLFinite (ofString "j") (.val (.word (index + 1)))
        (setVarHOLFinite (ofString "v") (.val (.word nextValue)) current)
      have nextNat : (index + 1).toNat = index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2^64; omega)]
        rfl
      have nextLocal : post.locals.lookup (ofString "j") = some (.val (.word (index + 1))) := by
        simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have nextField : post.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
        simpa [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "j" ≠ ofString "f" by decide,show ofString "v" ≠ ofString "f" by decide] using atField
      have nextWord : post.locals.lookup (ofString "v") = some (.val (.word nextValue)) := by
        simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "j" ≠ ofString "v" by decide]
      have postValid : invariant post := ⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,nextField,⟨nextValue,nextWord⟩⟩
      have rankNext : txScalarWordRank length post = length.toNat - (index + 1).toNat := by simp [txScalarWordRank,nextLocal]
      exact ⟨post,by rfl,by rfl,Or.inl ⟨advanced,postValid,by rw [rankNext,rankEq,nextNat]; omega⟩⟩
  have initialRank : txScalarWordRank length state = length.toNat - index.toNat := by simp [txScalarWordRank,indexLocal]
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,returned⟩ := evaluate_ranked_loop_return_property
    (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "f")))) txScalarWordStep
    invariant (txScalarWordRank length) 0 returnedProperty guard enter sameRank step state
    ⟨⟨index,indexLocal,bounded⟩,fieldLocal,⟨value,valueLocal⟩⟩ (by simpa [initialRank] using ticks)
  refine ⟨result,post,?_,by simpa [initialRank] using cost,remaining,noTimeout,?_,returned⟩
  · rw [source_txScalarWord_loop]; exact run
  · intro normal
    obtain ⟨⟨⟨found,binding,bounded⟩,atField,atValue⟩,rankZero⟩ := done normal
    have same : found = length := by
      apply BitVec.eq_of_toNat_eq
      simp [txScalarWordRank,binding] at rankZero
      omega
    exact ⟨by simpa [same] using binding,atField,atValue⟩

#print axioms evaluate_txScalarWord_loop_bounded
end InitECandidate.Runtime

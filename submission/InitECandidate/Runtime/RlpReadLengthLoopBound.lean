import InitECandidate.Runtime.RlpReadLengthStep
import InitECandidate.Runtime.RankedLoopReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpReadLengthRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

/-- The actual length-reader loop costs at most one tick per remaining byte,
including failed reads; all successful steps advance the source index. -/
theorem evaluate_rlpReadLength_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer index length value : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (bounded : index.toNat ≤ length.toNat) (ticks : length.toNat - index.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpReadLengthLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
        ∃ value : BitVec 64, post.locals.lookup (ofString "v") = some (.val (.word value))) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    (∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
    current.locals.lookup (ofString "n") = some (.val (.word length)) ∧
    current.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
    ∃ value : BitVec 64, current.locals.lookup (ofString "v") = some (.val (.word value))
  let returnedProperty := fun _ : ValueHOL 64 => False
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if rlpReadLengthRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength,atPointer,⟨value,atValue⟩⟩
    have rankEq : rlpReadLengthRank length current = length.toNat - index.toNat := by simp [rlpReadLengthRank,atIndex]
    by_cases inside : index.toNat < length.toNat
    · have nonzero : rlpReadLengthRank length current ≠ 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,nonzero]
    · have zero : rlpReadLengthRank length current = 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by intro current valid; exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F,
      rlpReadLengthRank length (decClockHOLFinite current) = rlpReadLengthRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < rlpReadLengthRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current rlpReadLengthStep = (none,post) ∧ invariant post ∧
          rlpReadLengthRank length post < rlpReadLengthRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current rlpReadLengthStep = (some result,post) ∧
           (∀ value, result = .returned value → returnedProperty value))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength,atPointer,⟨value,atValue⟩⟩ positive _
    have rankEq : rlpReadLengthRank length current = length.toNat - index.toNat := by simp [rlpReadLengthRank,atIndex]
    have inside : index.toNat < length.toNat := by rw [rankEq] at positive; omega
    rcases evaluate_rlpReadLength_step_cases current pointer index value atPointer atIndex atValue with failed | advanced
    · exact ⟨current,by omega,by omega,Or.inr ⟨.error,by simp,by simp,by simp,failed,by intro value impossible; cases impossible⟩⟩
    · obtain ⟨nextValue,advanced⟩ := advanced
      let post := setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
        (setVarHOLFinite (ofString "v") (.val (.word nextValue)) current)
      have nextNat : (index + 1).toNat = index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2^64; omega)]
        rfl
      have nextLocal : post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
        simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have nextLength : post.locals.lookup (ofString "n") = some (.val (.word length)) := by
        simpa [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "i" ≠ ofString "n" by decide,show ofString "v" ≠ ofString "n" by decide] using atLength
      have nextPointer : post.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
        simpa [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "i" ≠ ofString "p" by decide,show ofString "v" ≠ ofString "p" by decide] using atPointer
      have nextWord : post.locals.lookup (ofString "v") = some (.val (.word nextValue)) := by
        simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "i" ≠ ofString "v" by decide]
      have postValid : invariant post := ⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,nextLength,nextPointer,⟨nextValue,nextWord⟩⟩
      have rankNext : rlpReadLengthRank length post = length.toNat - (index + 1).toNat := by simp [rlpReadLengthRank,nextLocal]
      exact ⟨post,by rfl,by rfl,Or.inl ⟨advanced,postValid,by rw [rankNext,rankEq,nextNat]; omega⟩⟩
  have initialRank : rlpReadLengthRank length state = length.toNat - index.toNat := by simp [rlpReadLengthRank,indexLocal]
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,returned⟩ := evaluate_ranked_loop_return_property
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) rlpReadLengthStep
    invariant (rlpReadLengthRank length) 0 returnedProperty guard enter sameRank step state
    ⟨⟨index,indexLocal,bounded⟩,lengthLocal,pointerLocal,⟨value,valueLocal⟩⟩ (by simpa [initialRank] using ticks)
  refine ⟨result,post,?_,by simpa [initialRank] using cost,remaining,noTimeout,?_,returned⟩
  · rw [source_rlpReadLength_loop]; exact run
  · intro normal
    obtain ⟨⟨⟨found,binding,bounded⟩,atLength,atPointer,atValue⟩,rankZero⟩ := done normal
    have same : found = length := by
      apply BitVec.eq_of_toNat_eq
      simp [rlpReadLengthRank,binding] at rankZero
      omega
    exact ⟨by simpa [same] using binding,atLength,atPointer,atValue⟩

#print axioms evaluate_rlpReadLength_loop_bounded
end InitECandidate.Runtime

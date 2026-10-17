import InitECandidate.Runtime.CommonPrefixStep
import InitECandidate.Runtime.RankedLoopReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def commonPrefixRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

/-- Original prefix comparison consumes at most one tick per remaining byte.
Every early returned mismatch index is bounded by the comparison length. -/
theorem evaluate_commonPrefix_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index length : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat) (ticks : length.toNat - index.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state commonPrefixLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length))) ∧
      (∀ value, result = some (.returned value) → ∃ found : BitVec 64,
        value = .val (.word found) ∧ found.toNat ≤ length.toNat) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    (∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
    current.locals.lookup (ofString "n") = some (.val (.word length))
  let returnedProperty := fun value : ValueHOL 64 => ∃ found : BitVec 64,
    value = .val (.word found) ∧ found.toNat ≤ length.toNat
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if commonPrefixRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength⟩
    have rankEq : commonPrefixRank length current = length.toNat - index.toNat := by simp [commonPrefixRank,atIndex]
    by_cases inside : index.toNat < length.toNat
    · have nonzero : commonPrefixRank length current ≠ 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,nonzero]
    · have zero : commonPrefixRank length current = 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by intro current valid; exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F,
      commonPrefixRank length (decClockHOLFinite current) = commonPrefixRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < commonPrefixRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current commonPrefixStep = (none,post) ∧ invariant post ∧
          commonPrefixRank length post < commonPrefixRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current commonPrefixStep = (some result,post) ∧
           (∀ value, result = .returned value → returnedProperty value))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength⟩ positive _
    have rankEq : commonPrefixRank length current = length.toNat - index.toNat := by simp [commonPrefixRank,atIndex]
    have inside : index.toNat < length.toNat := by rw [rankEq] at positive; omega
    rcases evaluate_commonPrefix_step_cases current index atIndex with failed | returned | advanced
    · exact ⟨current,by omega,by omega,Or.inr ⟨.error,by simp,by simp,by simp,failed,by intro value impossible; cases impossible⟩⟩
    · refine ⟨emptyLocalsHOLFinite current,by rfl,by rfl,Or.inr ⟨.returned (.val (.word index)),by simp,by simp,by simp,returned,?_⟩⟩
      intro value equal
      have same := PanSemResultExact.returned.inj equal
      exact ⟨index,same.symm,bounded⟩
    · let post := setVarHOLFinite (ofString "i") (.val (.word (index + 1))) current
      have nextNat : (index + 1).toNat = index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2^64; omega)]
        rfl
      have nextLocal : post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
        simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have nextLength : post.locals.lookup (ofString "n") = some (.val (.word length)) := by
        simpa [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "i" ≠ ofString "n" by decide] using atLength
      have postValid : invariant post := ⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,nextLength⟩
      have rankNext : commonPrefixRank length post = length.toNat - (index + 1).toNat := by simp [commonPrefixRank,nextLocal]
      exact ⟨post,by rfl,by rfl,Or.inl ⟨advanced,postValid,by rw [rankNext,rankEq,nextNat]; omega⟩⟩
  have initialRank : commonPrefixRank length state = length.toNat - index.toNat := by simp [commonPrefixRank,indexLocal]
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,returned⟩ := evaluate_ranked_loop_return_property
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) commonPrefixStep
    invariant (commonPrefixRank length) 0 returnedProperty guard enter sameRank step state
    ⟨⟨index,indexLocal,bounded⟩,lengthLocal⟩ (by simpa [initialRank] using ticks)
  refine ⟨result,post,?_,by simpa [initialRank] using cost,remaining,noTimeout,?_,returned⟩
  · rw [source_commonPrefix_loop]; exact run
  · intro normal
    obtain ⟨⟨⟨found,binding,bounded⟩,atLength⟩,rankZero⟩ := done normal
    have same : found = length := by
      apply BitVec.eq_of_toNat_eq
      simp [commonPrefixRank,binding] at rankZero
      omega
    exact ⟨by simpa [same] using binding,atLength⟩

#print axioms evaluate_commonPrefix_loop_bounded
end InitECandidate.Runtime

import InitECandidate.Runtime.U256FromBeStepProgress
import InitECandidate.Runtime.StraightLocalOutcomes
import InitECandidate.Runtime.RankedLoopReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def u256FromBeRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

theorem u256FromBe_step_localOnly : straightLocalOnly u256FromBeStep = true := by
  simp only [u256FromBeStep,u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The general converter loop uses at most one clock per remaining byte.
Malformed locals and inaccessible bytes terminate rather than invalidating the bound. -/
theorem evaluate_u256FromBe_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index length : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat) (ticks : length.toNat - index.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state u256FromBeLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word length))) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    (∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
    current.locals.lookup (ofString "n") = some (.val (.word length))
  let returnedProperty := fun _ : ValueHOL 64 => False
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if u256FromBeRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength⟩
    have rankEq : u256FromBeRank length current = length.toNat - index.toNat := by simp [u256FromBeRank,atIndex]
    by_cases inside : index.toNat < length.toNat
    · have nonzero : u256FromBeRank length current ≠ 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : u256FromBeRank length current = 0 := by rw [rankEq]; omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atLength,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by intro current valid; exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F,
      u256FromBeRank length (decClockHOLFinite current) = u256FromBeRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < u256FromBeRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current u256FromBeStep = (none,post) ∧ invariant post ∧
          u256FromBeRank length post < u256FromBeRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current u256FromBeStep = (some result,post) ∧
           (∀ value, result = .returned value → returnedProperty value))) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atLength⟩ positive _
    have rankEq : u256FromBeRank length current = length.toNat - index.toNat := by simp [u256FromBeRank,atIndex]
    have inside : index.toNat < length.toNat := by rw [rankEq] at positive; omega
    have clock := (evaluate_u256FromBe_step_clock current).1
    have outcomes := evaluate_straightLocal_outcomes u256FromBeStep u256FromBe_step_localOnly current
    cases run : evaluateHOLFiniteState current u256FromBeStep with
    | mk result post =>
      rw [run] at clock outcomes
      dsimp only at clock outcomes
      refine ⟨post,by omega,by omega,?_⟩
      rcases outcomes with normal | error
      · subst result
        have progress := evaluate_u256FromBe_step_progress current post index atIndex run
        have nextNat : (index + 1).toNat = index.toNat + 1 := by
          rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2^64; omega)]
          rfl
        have nextLength := progress.2.2.trans atLength
        have nextRank : u256FromBeRank length post = length.toNat - (index + 1).toNat := by
          simp [u256FromBeRank,progress.1]
        exact Or.inl ⟨rfl,⟨⟨index + 1,progress.1,by rw [nextNat]; omega⟩,nextLength⟩,
          by rw [nextRank,rankEq,nextNat]; omega⟩
      · subst result
        exact Or.inr ⟨.error,by simp,by simp,by simp,rfl,by intro value impossible; cases impossible⟩
  have initialRank : u256FromBeRank length state = length.toNat - index.toNat := by simp [u256FromBeRank,indexLocal]
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,returned⟩ := evaluate_ranked_loop_return_property
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) u256FromBeStep
    invariant (u256FromBeRank length) 0 returnedProperty guard enter sameRank step state
    ⟨⟨index,indexLocal,bounded⟩,lengthLocal⟩ (by simpa [initialRank] using ticks)
  refine ⟨result,post,?_,by simpa [initialRank] using cost,remaining,noTimeout,?_,returned⟩
  · rw [source_u256FromBe_loop]; exact run
  · intro normal
    obtain ⟨⟨⟨found,binding,bounded⟩,atLength⟩,rankZero⟩ := done normal
    have same : found = length := by
      apply BitVec.eq_of_toNat_eq
      simp [u256FromBeRank,binding] at rankZero
      omega
    exact ⟨by simpa [same] using binding,atLength⟩

#print axioms evaluate_u256FromBe_loop_bounded
end InitECandidate.Runtime

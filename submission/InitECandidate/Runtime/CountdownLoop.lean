import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.NoTopBreak
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def countdownAssign (key : MlS) : ProgHOL 64 :=
  .assign .local key (.op .sub [.var .local key,.const 1])

def CountdownRank (key : MlS) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ word : BitVec 64, state.locals.lookup key = some (.val (.word word)) ∧ word.toNat ≤ rank

theorem evaluate_countdown_assign {F : Type} (state : PanSemStateFiniteExact 64 F) (key : MlS)
    (word : BitVec 64) (counter : state.locals.lookup key = some (.val (.word word))) :
    evaluateHOLFiniteState state (countdownAssign key) =
      (none,setVarHOLFinite key (.val (.word (word - (1#64)))) state) := by
  simp [countdownAssign,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,counter,
    wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,
    shapeOfHOLExact,shapeEqHOL]

theorem countdown_ranked (key : MlS) (tail : ProgHOL 64) (cost : Nat)
    (tailBound : ProgBounded tail cost) (keeps : avoidsLocal key tail = true)
    (noCont : noTopContinue tail = true) (noBreak : noTopBreak tail = true) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      CountdownRank key state rank → rank * (cost + 1) ≤ state.clock →
      RankedOutcome state (.cmp .notEqual (.var .local key) (.const 0)) (rank * (cost + 1))
        (CountdownRank key) False
        (evaluateHOLFiniteState state (.while (.cmp .notEqual (.var .local key) (.const 0))
          (.seq (countdownAssign key) tail))) := by
  refine rankedWhile_run _ _ cost (CountdownRank key) False ?_ ?_
  · intro F state ranked word guard
    obtain ⟨counter,atCounter,zero⟩ := ranked
    have counterZero : counter = 0 := BitVec.eq_of_toNat_eq (by change counter.toNat = 0; omega)
    subst counter
    simpa [evalHOLExact,atCounter,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm
  · intro F state rank word code ranked guard running budget
    obtain ⟨counter,atCounter,within⟩ := ranked
    have positive : 0 < counter.toNat := by
      by_contra stopped
      have zero : counter = 0 := BitVec.eq_of_toNat_eq (by change counter.toNat = 0; omega)
      subst counter
      exact running (by simpa [evalHOLExact,atCounter,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm)
    let entered := setVarHOLFinite key (.val (.word (counter - (1#64)))) (decClockHOLFinite state)
    have assigned := evaluate_countdown_assign (decClockHOLFinite state) key counter atCounter
    have bodyEval : evaluateHOLFiniteState (decClockHOLFinite state) (.seq (countdownAssign key) tail) =
        evaluateHOLFiniteState entered tail := by
      rw [evaluateHOLFiniteState_seq_line780,assigned]
    have tailRun := tailBound entered (by exact code) (by change cost ≤ state.clock - 1; omega)
    have bodyBound : RunBounded (decClockHOLFinite state) (.seq (countdownAssign key) tail) cost := by
      unfold RunBounded
      rw [bodyEval]
      exact tailRun
    have noContinue := evaluate_noTopContinue tail noCont entered
    have noBreaking := evaluate_noTopBreak tail noBreak entered
    refine ⟨bodyBound.1,bodyBound.2.1,bodyBound.2.2,?_,?_⟩
    · intro flow
      rw [bodyEval] at flow ⊢
      rcases flow with normal | cont
      · have frame := evaluate_avoidsLocal_flowing key tail keeps entered (Or.inl normal)
        have after : (evaluateHOLFiniteState entered tail).2.locals.lookup key =
            some (.val (.word (counter - (1#64)))) := by
          rw [frame]; simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        have natural : (counter - (1#64)).toNat = counter.toNat - 1 :=
          BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ counter.toNat; omega))
        have meta' := evaluateHOLFiniteState_metadata entered tail
        exact ⟨rank,le_refl _,⟨counter - (1#64),after,by omega⟩,meta'.1⟩
      · exact absurd cont noContinue
    · rw [bodyEval]
      intro broken
      exact absurd broken noBreaking

#print axioms evaluate_countdown_assign
#print axioms countdown_ranked
end InitECandidate.Runtime

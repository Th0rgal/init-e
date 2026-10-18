import InitECandidate.Runtime.CeilLog2Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ceilLog2Increment : ProgHOL 64 := .assign .local (ofString "d")
  (.op .add [.var .local (ofString "d"),.const 1])

theorem evaluate_ceilLog2_increment {F : Type} (state : PanSemStateFiniteExact 64 F)
    (d : BitVec 64) (counter : state.locals.lookup (ofString "d") = some (.val (.word d))) :
    evaluateHOLFiniteState state ceilLog2Increment =
      (none,setVarHOLFinite (ofString "d") (.val (.word (d + 1))) state) := by
  simp [ceilLog2Increment,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,counter,
    wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,
    setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]

/-- A normal original ceil-log loop exit has a legal shift amount and a false
guard. In particular, reaching the rejecting width-64 guard is not a return. -/
theorem ceilLog2_loop_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (d : BitVec 64) (counter : state.locals.lookup (ofString "d") = some (.val (.word d)))
    (within : d.toNat ≤ 64)
    (run : evaluateHOLFiniteState state (.while ceilLog2Condition ceilLog2Increment) = (none,post)) :
    ∃ result : BitVec 64, result.toNat < 64 ∧
      post.locals.lookup (ofString "d") = some (.val (.word result)) ∧
      evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
        ceilLog2Condition = some (.val (.word (0#64))) := by
  have atWidthImpossible (guard : evalHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) ceilLog2Condition ≠ none) :
      d.toNat < 64 := by
    by_contra notSmall
    have equal : d = (64 : BitVec 64) := BitVec.eq_of_toNat_eq (by simp; omega)
    exact guard (ceilLog2_guard_at_width state (by simpa only [equal] using counter))
  rw [evaluateHOLFiniteState_while_total] at run
  cases guardRun : evalHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) ceilLog2Condition with
  | none => rw [guardRun] at run; cases run
  | some value =>
    cases value with
    | rStruct fields => rw [guardRun] at run; cases run
    | nStruct name fields => rw [guardRun] at run; cases run
    | val word =>
      cases word with
      | word test =>
        have small : d.toNat < 64 := atWidthImpossible (by rw [guardRun]; simp)
        rw [guardRun] at run
        dsimp only at run
        by_cases zero : test = (0#64)
        · simp [zero] at run
          subst post
          exact ⟨d,small,counter,by simpa only [zero] using guardRun⟩
        · have clock : state.clock ≠ 0 := by
            intro empty
            simp [zero,empty] at run
          have increment := evaluate_ceilLog2_increment (decClockHOLFinite state) d counter
          have recursive : evaluateHOLFiniteState
              (setVarHOLFinite (ofString "d") (.val (.word (d + 1))) (decClockHOLFinite state))
              (.while ceilLog2Condition ceilLog2Increment) = (none,post) := by
            have nonzero : test ≠ (0 : BitVec 64) := by simpa using zero
            simp only [nonzero,ne_eq,zero,not_false_eq_true,if_true,if_false] at run
            rw [if_neg clock,fixClockHOLFinite_evaluateState,increment] at run
            simpa [fixClockHOLFinite,setVarHOLFinite,decClockHOLFinite] using run
          have natural : (d + 1).toNat = d.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by simp; omega)]
            rfl
          exact ceilLog2_loop_returned _ post (d + 1)
            (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
            (by rw [natural]; omega) recursive
termination_by state.clock
decreasing_by simp [setVarHOLFinite,decClockHOLFinite]; omega

#print axioms evaluate_ceilLog2_increment
#print axioms ceilLog2_loop_returned
end InitECandidate.Runtime

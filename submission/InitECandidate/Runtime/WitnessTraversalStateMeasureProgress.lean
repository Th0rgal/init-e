import InitECandidate.Runtime.WitnessTraversalStateMeasure
import InitECandidate.Runtime.WitnessModeCallerLocals
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witnessTraversalStateMeasure_positive {F : Type} (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64)))) :
    0<witnessTraversalStateMeasure frame s := by
  classical
  have nonzero : s.locals.lookup (ofString "go")≠some (.val (.word (0 : BitVec 64))) := by
    rw [running]; simp
  have modePositive : 0<witnessTraversalModeCredit s := by
    unfold witnessTraversalModeCredit
    split
    · omega
    · split <;> omega
  rw [witnessTraversalStateMeasure,if_neg nonzero]
  unfold decodeWitnessMeasure
  omega

theorem witnessTraversalStateMeasure_stopped {F : Type} (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
    (stopped : s.locals.lookup (ofString "go")=some (.val (.word (0#64)))) :
    witnessTraversalStateMeasure frame s=0 := by
  classical
  change s.locals.lookup (ofString "go")=some (.val (.word (0 : BitVec 64))) at stopped
  rw [witnessTraversalStateMeasure,if_pos stopped]

/-- Checked component inequalities become inequalities of the same state
measure through actual local bindings on each side. -/
theorem witnessTraversalStateMeasure_decreases_of_running {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (frame top nextTop : BitVec 64) (mode nextMode : Nat)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (postRunning : post.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (nextAtTop : post.locals.lookup (ofString "top")=some (.val (.word nextTop)))
    (modeCredit : witnessTraversalModeCredit s=mode) (nextModeCredit : witnessTraversalModeCredit post=nextMode)
    (rank : decodeWitnessMeasure (decoderScratchCapacity frame post) nextTop (witnessTraversalChildCredit post nextTop) nextMode <
      decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) mode) :
    witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  rw [witnessTraversalStateMeasure_running s frame top running atTop,
    witnessTraversalStateMeasure_running post frame nextTop postRunning nextAtTop,modeCredit,nextModeCredit]
  exact rank

theorem witness_unwind_nonempty_mode_go_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F) (top : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top))) (nonempty : top≠0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "go")=s.locals.lookup (ofString "go") := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,show top≠0#64 from nonempty]
  rw [evaluation] at run
  exact witness_unwind_nonempty_go_normal_kept s post run

theorem witness_unwind_empty_state_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word (0#64))))
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  have postEq := witness_unwind_empty_normal_progress s post atTop run
  have stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
    rw [postEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [witnessTraversalStateMeasure_stopped post frame stopped]
  exact witnessTraversalStateMeasure_positive s frame running

#print axioms witnessTraversalStateMeasure_positive
#print axioms witnessTraversalStateMeasure_stopped
#print axioms witnessTraversalStateMeasure_decreases_of_running
#print axioms witness_unwind_nonempty_mode_go_normal_kept
#print axioms witness_unwind_empty_state_measure_decreases
end InitECandidate.Runtime

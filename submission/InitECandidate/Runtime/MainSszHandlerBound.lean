import InitECandidate.Runtime.MainSszHandlerSource
import InitECandidate.Runtime.SerializeResultCallBound
import InitECandidate.Runtime.OutputWriteCallBound
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.ByteStoresControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_mainSszHalt_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let evaluated := evaluateHOLFiniteState state mainSszHalt
    state.clock ≤ evaluated.2.clock ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := evaluate_external_call_clock state (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)
  have safe := evaluate_external_call_no_timeout state (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)
  exact evaluate_sequence_straight_bounded state _ (.return (.const 1)) 0
    ⟨by rw [ticks]; omega,by rw [ticks],safe⟩ (by rfl)

/-- After serialization, the original rejection handler writes exactly
44 bytes and halts within 45 source clocks. -/
theorem evaluate_mainSszOutput_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word 43)))
    (code : state.code = originalRuntimeCode) (budget : 45 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state mainSszOutput
    state.clock ≤ evaluated.2.clock + 45 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have frame := evaluate_storeByte_control_frame state
    (.op .add [.var .local (ofString "out"),.var .local (ofString "n")]) (.var .local (ofString "err_code"))
  change ((evaluateHOLFiniteState state mainSszErrorStore).1 = none ∨
    (evaluateHOLFiniteState state mainSszErrorStore).1 = some .error) ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.clock = state.clock ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.locals = state.locals ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.globals = state.globals ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.code = state.code ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.memaddrs = state.memaddrs ∧
    (evaluateHOLFiniteState state mainSszErrorStore).2.be = state.be at frame
  rw [mainSszOutput,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state mainSszErrorStore with
  | mk result next =>
    rw [stored] at frame
    dsimp only at frame ⊢
    obtain ⟨control,clock,locals,_,installed,_,_⟩ := frame
    rcases control with rfl | rfl
    · have arguments : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
        mainSszOutputArguments = some [.val (.word output),.val (.word 44)] := by
        simp [mainSszOutputArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,atOutput,atLength,
          wordOpHOL,wordOp,valueIsWord,valueWord]
      have call := evaluate_outputWrite_call_bounded next none mainSszOutputArguments output 44 arguments
        (installed.trans code) (by change 45 ≤ next.clock; omega)
      change next.clock ≤ (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainSszOutputArguments)).2.clock + 45 ∧
        (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainSszOutputArguments)).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainSszOutputArguments)).1 ≠ some .timeOut at call
      have tail := evaluate_sequence_code_bounded next _ mainSszHalt 45 0 call
        (fun current _ _ => evaluate_mainSszHalt_bounded current) (by omega)
      dsimp only
      exact ⟨by have spent := tail.1; omega,by have kept := tail.2.1; omega,tail.2.2⟩
    · dsimp only
      exact ⟨by omega,by omega,by simp⟩

/-- The exact SSZ rejection handler in original main, including result
serialization, diagnostic byte, output write and halt, costs at most 65
source clocks. Invalid accesses and early host termination are covered. -/
theorem evaluate_mainSszHandler_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output zeroRoot : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atZeroRoot : state.locals.lookup (ofString "z32") = some (.val (.word zeroRoot)))
    (code : state.code = originalRuntimeCode) (budget : 65 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state mainSszHandler
    state.clock ≤ evaluated.2.clock + 65 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      mainSszSerializeArguments =
        some [.val (.word output),.val (.word zeroRoot),.val (.word 0),.val (.word 0),.val (.word 0)] := by
    simp [mainSszSerializeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atOutput,atZeroRoot]
  apply evaluate_serializeResult_continuation_bounded state (ofString "n") mainSszOutput 45
    mainSszSerializeArguments output zeroRoot 0 0 0 arguments code budget
  intro ready locals installed domain enough
  apply evaluate_mainSszOutput_bounded ready output ?_ ?_ (installed.trans code) enough
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atOutput,show ofString "n" ≠ ofString "out" by decide]
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_mainSszHalt_bounded
#print axioms evaluate_mainSszOutput_bounded
#print axioms evaluate_mainSszHandler_bounded
end InitECandidate.Runtime

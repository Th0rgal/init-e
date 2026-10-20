import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.MainNormalOutputSource
import InitECandidate.Runtime.SerializeResultCallBound
import InitECandidate.Runtime.OutputWriteCallBound
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.ByteStoresControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_mainNormalHalt_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let evaluated := evaluateHOLFiniteState state mainNormalHalt
    state.clock ≤ evaluated.2.clock ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := evaluate_external_call_clock state (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)
  have safe := evaluate_external_call_no_timeout state (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)
  exact evaluate_sequence_straight_bounded state _ (.return (.const 0)) 0
    ⟨by rw [ticks]; omega,by rw [ticks],safe⟩ (by rfl)

/-- After serialization, the original normal output path writes exactly
44 bytes and halts within 45 source clocks. -/
theorem evaluate_mainNormalOutput_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word 43)))
    (code : state.code = originalRuntimeCode) (budget : 45 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state mainNormalOutput
    state.clock ≤ evaluated.2.clock + 45 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have frame := evaluate_storeByte_control_frame state
    (.op .add [.var .local (ofString "out"),.var .local (ofString "n")]) (.var .global (ofString "fail_code"))
  change ((evaluateHOLFiniteState state mainNormalErrorStore).1 = none ∨
    (evaluateHOLFiniteState state mainNormalErrorStore).1 = some .error) ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.clock = state.clock ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.locals = state.locals ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.globals = state.globals ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.code = state.code ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.memaddrs = state.memaddrs ∧
    (evaluateHOLFiniteState state mainNormalErrorStore).2.be = state.be at frame
  rw [mainNormalOutput,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state mainNormalErrorStore with
  | mk result next =>
    rw [stored] at frame
    dsimp only at frame ⊢
    obtain ⟨control,clock,locals,_,installed,_,_⟩ := frame
    rcases control with rfl | rfl
    · have arguments : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
        mainNormalOutputArguments = some [.val (.word output),.val (.word 44)] := by
        simp [mainNormalOutputArguments,mainSszOutputArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,atOutput,atLength,
          wordOpHOL,wordOp,valueIsWord,valueWord]
      have call := evaluate_outputWrite_call_bounded next none mainNormalOutputArguments output 44 arguments
        (installed.trans code) (by change 45 ≤ next.clock; omega)
      change next.clock ≤ (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainNormalOutputArguments)).2.clock + 45 ∧
        (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainNormalOutputArguments)).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next
          (.call (some (none,none)) (ofString "output_write") mainNormalOutputArguments)).1 ≠ some .timeOut at call
      have tail := evaluate_sequence_code_bounded next _ mainNormalHalt 45 0 call
        (fun current _ _ => evaluate_mainNormalHalt_bounded current) (by omega)
      dsimp only
      exact ⟨by have spent := tail.1; omega,by have kept := tail.2.1; omega,tail.2.2⟩
    · dsimp only
      exact ⟨by omega,by omega,by simp⟩

/-- The exact successful-decode output suffix in original main, including result
serialization, diagnostic byte, output write and halt, costs at most 65
source clocks. Invalid accesses and early host termination are covered. -/
theorem evaluate_mainNormalSerialization_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output root success si chain : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (atSuccess : state.locals.lookup (ofString "succ") = some (.val (.word success)))
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (chainDomain : state.memaddrs (si + (88#64)))
    (chainCell : state.memory (si + (88#64))=.word chain)
    (code : state.code = originalRuntimeCode) (budget : 65 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state mainNormalSerialization
    state.clock ≤ evaluated.2.clock + 65 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      mainNormalSerializeArguments =
        some [.val (.word output),.val (.word root),.val (.word success),.val (.word chain),.val (.word 5377)] := by
    simp [mainNormalSerializeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atOutput,atRoot,
      atSuccess,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,chainDomain,chainCell]
  apply evaluate_serializeResult_continuation_bounded state (ofString "n") mainNormalOutput 45
    mainNormalSerializeArguments output root success chain 5377 arguments code budget
  intro ready locals installed domain enough
  apply evaluate_mainNormalOutput_bounded ready output ?_ ?_ (installed.trans code) enough
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atOutput,show ofString "n" ≠ ofString "out" by decide]
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_mainNormalHalt_bounded
#print axioms evaluate_mainNormalOutput_bounded
#print axioms evaluate_mainNormalSerialization_bounded
/-- Original main after verification serializes and emits its result within65 ticks. -/
theorem runBounded_main_normal_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
 (output root success si chain : BitVec 64)
 (atOutput : state.locals.lookup (ofString "out")=some (.val (.word output)))
 (atRoot : state.locals.lookup (ofString "root")=some (.val (.word root)))
 (atSuccess : state.locals.lookup (ofString "succ")=some (.val (.word success)))
 (atSi : state.locals.lookup (ofString "si")=some (.val (.word si)))
 (chainDomain : state.memaddrs (si+(88#64)))
 (chainCell : state.memory (si+(88#64))=.word chain)
 (code : state.code=originalRuntimeCode) (budget : 65≤state.clock) :
 RunBounded state (mainAt 24) 65 := by
 rw [source_main_normal_serialization]
 exact evaluate_mainNormalSerialization_bounded state output root success si chain atOutput atRoot atSuccess atSi
  chainDomain chainCell code budget
#print axioms runBounded_main_normal_suffix
end InitECandidate.Runtime

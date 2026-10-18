import InitECandidate.Runtime.MainAllInitializersCells
import InitECandidate.Runtime.InputBlobDeclarationReach
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def MainInputReady {F : Type} (state ready : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ initialized, AllInitializerContinuation state initialized ∧
    InputBlobReady initialized (ofString "inp") 2713731432 ready

/-- Compose the actual complete initialization and declared input reader.
The normal path carries the initialized globals and bounded input geometry. -/
theorem main_initialization_input_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (budget : 1893 + (inputBlobBodyCost + 1) ≤ state.clock)
    (initialization : Reaches state (mainAt 0) (AllInitializerContinuation state) 1893 (mainAt 14)) :
    Reaches state (mainAt 0) (MainInputReady state)
      (1893 + (inputBlobBodyCost + 1)) (mainAt 15) := by
  rcases initialization with ⟨initialized,valid,spent,remaining,agreement⟩ | aborted
  · have input := evaluate_inputBlob_declaration_reaches initialized (ofString "inp") 2713731432
      (mainAt 15) valid.2.2.2.2 (by decide) (valid.2.1.trans code) (by omega)
    rw [← source_main_input_declaration] at input
    rcases input with ⟨ready,inputReady,inputSpent,inputRemaining,inputAgreement⟩ | aborted
    · left
      exact ⟨ready,⟨initialized,valid,inputReady⟩,by omega,by omega,
        scoped_trans agreement inputAgreement⟩
    · right
      obtain ⟨result,terminal,noReturn,inputSpent,inputRemaining,noTimeout⟩ := aborted
      refine ⟨result,agreement.1.trans terminal,noReturn,?_,?_,?_⟩
      · rw [agreement.2.1]; omega
      · rw [agreement.2.1]; omega
      · intro _
        exact noTimeout (by omega)
  · right
    exact stAbort_mono state _ 1893 (1893 + (inputBlobBodyCost + 1)) (by omega) aborted

#print axioms main_initialization_input_reaches
end InitECandidate.Runtime

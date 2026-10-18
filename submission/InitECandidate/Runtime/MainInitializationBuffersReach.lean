import InitECandidate.Runtime.MainInitializationInputReach
import InitECandidate.Runtime.MainBufferDeclarationsReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def MainBuffersReady {F : Type} (state ready : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ inputState pointer, MainInputReady state inputState ∧
    inputState.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
    MainBufferDeclarationsReady inputState pointer ready

theorem main_initialization_buffers_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (budget : (1893 + (inputBlobBodyCost + 1)) + 4 ≤ state.clock)
    (inputRun : Reaches state (mainAt 0) (MainInputReady state)
      (1893 + (inputBlobBodyCost + 1)) (mainAt 15)) :
    Reaches state (mainAt 0) (MainBuffersReady state)
      ((1893 + (inputBlobBodyCost + 1)) + 4) (mainAt 17) := by
  rcases inputRun with ⟨inputState,valid,spent,remaining,agreement⟩ | aborted
  · have fields := valid
    obtain ⟨initialized,initValid,length,_,_,globals,capped,_,_,installed,_⟩ := fields
    let pointer := allocationEnd 2713731432 (length + 8)
    have inputHeap : inputState.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
      rw [globals]
      simp [pointer,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have buffers := main_buffer_declarations_reaches inputState pointer
      (installed.trans (initValid.2.1.trans code)) inputHeap capped (by omega)
    rcases buffers with ⟨ready,bufferValid,bufferSpent,bufferRemaining,bufferAgreement⟩ | aborted
    · left
      exact ⟨ready,⟨inputState,pointer,valid,inputHeap,bufferValid⟩,by omega,by omega,
        scoped_trans agreement bufferAgreement⟩
    · right
      obtain ⟨result,terminal,noReturn,bufferSpent,bufferRemaining,noTimeout⟩ := aborted
      refine ⟨result,agreement.1.trans terminal,noReturn,?_,?_,?_⟩
      · rw [agreement.2.1]; omega
      · rw [agreement.2.1]; omega
      · intro _
        exact noTimeout (by omega)
  · right
    exact stAbort_mono state _ (1893 + (inputBlobBodyCost + 1))
      ((1893 + (inputBlobBodyCost + 1)) + 4) (by omega) aborted

#print axioms main_initialization_buffers_reaches
end InitECandidate.Runtime

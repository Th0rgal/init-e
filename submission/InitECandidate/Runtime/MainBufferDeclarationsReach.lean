import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def MainBufferDeclarationsReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (ready : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ middle, AllocationDeclarationReady state (ofString "out") pointer 256 middle ∧
    AllocationDeclarationReady middle (ofString "z32") (allocationEnd pointer 256) 32 ready

/-- Main's two output-buffer declarations reach zeroing or abort in four
ticks, retaining the exact heap and caller-binding relationships. -/
theorem main_buffer_declarations_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (budget : 4 ≤ state.clock) :
    Reaches state (mainAt 15) (MainBufferDeclarationsReady state pointer) 4 (mainAt 17) := by
  have first := evaluate_allocation_declaration_reaches state (.const 256) (ofString "out")
    pointer 256 (mainAt 16) (by rfl) code heap pointerBound (by omega)
  rw [← source_main_output_declaration] at first
  rcases first with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · have fields := valid
    obtain ⟨_,_,installed,_,globals,capped,_,_⟩ := fields
    have midHeap : middle.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationEnd pointer 256))) := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have second := evaluate_allocation_declaration_reaches middle (.const 32) (ofString "z32")
      (allocationEnd pointer 256) 32 (mainAt 17) (by rfl) (installed.trans code) midHeap capped (by omega)
    rw [← source_main_zero_declaration] at second
    rcases second with ⟨ready,secondValid,secondSpent,secondRemaining,secondAgreement⟩ | aborted
    · left
      exact ⟨ready,⟨middle,valid,secondValid⟩,by omega,by omega,
        scoped_trans agreement secondAgreement⟩
    · right
      obtain ⟨result,terminal,noReturn,secondSpent,secondRemaining,noTimeout⟩ := aborted
      refine ⟨result,agreement.1.trans terminal,noReturn,?_,?_,?_⟩
      · rw [agreement.2.1]; omega
      · rw [agreement.2.1]; omega
      · intro _
        exact noTimeout (by omega)
  · right
    exact stAbort_mono state _ 2 4 (by omega) aborted

#print axioms main_buffer_declarations_reaches
end InitECandidate.Runtime

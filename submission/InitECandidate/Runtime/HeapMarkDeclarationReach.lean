import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def HeapMarkDeclarationReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (ready : PanSemStateFiniteExact 64 F) : Prop :=
  ready.locals = state.locals.update (name,.val (.word pointer)) ∧
    ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs

/-- The original marker declaration reaches its actual continuation in one
call-entry tick while preserving the complete memory/global state. -/
theorem evaluate_heapMark_declaration_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (budget : 1 ≤ state.clock) :
    Reaches state (.decCall name .one (ofString "heap_mark") [] continuation)
      (HeapMarkDeclarationReady state name pointer) 1 continuation := by
  obtain ⟨marked,_,clock,memory,globals,locals,installed,domain,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state pointer code heap (by omega)
  let ready := setVarHOLFinite name (.val (.word pointer)) marked
  left
  refine ⟨ready,⟨?_,memory,globals,installed,domain⟩,?_,?_,?_⟩
  · change marked.locals.update _ = _
    rw [locals]
  · change state.clock ≤ marked.clock + 1
    omega
  · change marked.clock ≤ state.clock
    omega
  · rw [declaration]
    exact scoped_restore (evaluateHOLFiniteState ready continuation) _

#print axioms evaluate_heapMark_declaration_reaches
end InitECandidate.Runtime

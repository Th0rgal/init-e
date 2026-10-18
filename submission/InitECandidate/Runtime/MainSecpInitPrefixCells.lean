import InitECandidate.Runtime.MainSecpInitPrefix
import InitECandidate.Runtime.SecpInitActualHeapCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem evaluate_main_secpInit_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718280)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713718280 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 4 ≤ state.clock) :
    ∃ next : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (mainAt 6) = evaluateHOLFiniteState next (mainAt 7) ∧
      next.clock = state.clock - 4 ∧ next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
      next.locals = state.locals ∧ next.memory = secpInitMemory state.memory 2713718280 ∧
      next.globals = secpInitActualGlobals state.globals ∧
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)) := by
  obtain ⟨next,call,clock,memory,locals,installed,domain,_,scratch,finalHeap,other⟩ :=
    evaluate_secp256k1Init_call_at_entry_heap_cells state code heap zero arena budget
  refine ⟨next,?_,clock,installed,domain,locals,memory,?_,finalHeap⟩
  · rw [source_main_secpInit_call,evaluateHOLFiniteState_seq_line780,call]
  · apply HolFiniteMapExact.ext
    funext key
    by_cases atScratch : key = ofString "secp_accel_scratch"
    · subst key
      simpa [secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE] using scratch
    · by_cases atHeap : key = ofString "heap_ptr"
      · subst key
        simpa [secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm atScratch] using finalHeap
      · simpa [secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE,
          Ne.symm atScratch,Ne.symm atHeap] using other key atScratch atHeap

#print axioms evaluate_main_secpInit_prefix_cells
end InitECandidate.Runtime

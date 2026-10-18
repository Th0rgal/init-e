import InitECandidate.Runtime.MainHeaderInitReach
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.HeaderInitCallSuccessCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_main_headerInit_reaches_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0)))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + 8 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 11 ≤ state.clock) :
    Reaches state (mainAt 11) (HeaderInitContinuation state pointer) 11 (mainAt 12) := by
  obtain ⟨next,call,spent,remaining,_,locals,installed,domain,header,heapEnd,other⟩ :=
    evaluate_headerInit_call_success_cells state pointer code heap zero aligned room arena budget
  have globals : next.globals = headerInitGlobals state.globals pointer := by
    apply HolFiniteMapExact.ext
    funext key
    by_cases atHeader : key = ofString "hdr_zero8"
    · subst key
      simpa [headerInitGlobals,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE] using header
    · by_cases atHeap : key = ofString "heap_ptr"
      · subst key
        simpa [headerInitGlobals,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using heapEnd
      · simpa [headerInitGlobals,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,
          Ne.symm atHeader,Ne.symm atHeap] using other key atHeader atHeap
  refine Or.inl ⟨next,⟨globals,locals,installed,domain,heapEnd⟩,spent,remaining,?_⟩
  rw [source_main_headerInit_call,evaluateHOLFiniteState_seq_line780,call]
  exact scoped_refl _

#print axioms evaluate_main_headerInit_reaches_cells
end InitECandidate.Runtime

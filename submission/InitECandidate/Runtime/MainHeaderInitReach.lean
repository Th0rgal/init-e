import InitECandidate.Runtime.HeaderInitCallSuccess
import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def headerInitGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  globalAllocationGlobals globals pointer [(ofString "hdr_zero8",8)]

def HeaderInitContinuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = headerInitGlobals state.globals pointer ∧ next.locals = state.locals ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 8)))

theorem headerInitGlobals_lookup_other (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) (key : MlS) (notHeap : key ≠ ofString "heap_ptr")
    (notHeader : key ≠ ofString "hdr_zero8") :
    (headerInitGlobals globals pointer).lookup key = globals.lookup key := by
  apply globalAllocationGlobals_lookup_other globals pointer [(ofString "hdr_zero8",8)] key notHeap
  intro entry member
  simp only [List.mem_singleton] at member
  subst entry
  exact notHeader

theorem source_main_headerInit_call : mainAt 11 =
    .seq (.call (some (none,none)) (ofString "header_init") []) (mainAt 12) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original header initializer reaches EVM initialization with its
computed allocation globals and heap frontier within eleven source ticks. -/
theorem evaluate_main_headerInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0)))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + 8 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 11 ≤ state.clock) :
    Reaches state (mainAt 11) (HeaderInitContinuation state pointer) 11 (mainAt 12) := by
  obtain ⟨next,call,spent,remaining,_,locals,installed,domain,header,heapEnd,other⟩ :=
    evaluate_headerInit_call_success state pointer code heap zero aligned room arena budget
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

#print axioms source_main_headerInit_call
#print axioms evaluate_main_headerInit_reaches
end InitECandidate.Runtime

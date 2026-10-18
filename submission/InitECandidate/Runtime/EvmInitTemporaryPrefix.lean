import InitECandidate.Runtime.EvmInitTemporarySource
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationPlanAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def EvmTemporaryReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = state.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 40))) ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    next.locals.lookup (ofString "mark") = some (.val (.word pointer)) ∧
    next.locals.lookup (ofString "s") = some (.val (.word pointer))

/-- Save the frontier and allocate the actual temporary string buffer. The
source declarations retain their scope restoration in the execution summary. -/
theorem evaluate_evmInit_temporary_declarations {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 40 ≤ 33806089496)
    (budget : 2 ≤ state.clock) :
    Reaches state (evmInitAt 0) (EvmTemporaryReady state pointer) 2 (evmInitAt 2) := by
  obtain ⟨markedPost,_,markClock,_,markGlobals,markLocals,markCode,markDomain,_,markDeclaration⟩ :=
    evaluate_heapMark_call_and_declaration state pointer code heap (by omega)
  let marked := setVarHOLFinite (ofString "mark") (.val (.word pointer)) markedPost
  have markedHeap : marked.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    change markedPost.globals.lookup _ = _
    rw [markGlobals]
    exact heap
  have safe := (allocationPlan_safe_aligned [40] pointer aligned
    (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
    (by simpa using small)).1
  obtain ⟨allocated,_,allocationClock,_,allocationLocals,allocationCode,allocationDomain,_,_,allocationGlobals,allocationDeclaration⟩ :=
    evaluate_alloc_call_and_declaration marked (.const 40) pointer 40
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) (markCode.trans code)
      (by change markedPost.clock ≠ 0; omega) markedHeap safe.1 safe.2.1
  let ready := setVarHOLFinite (ofString "s") (.val (.word pointer)) allocated
  have readyGlobals : ready.globals =
      state.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 40))) := by
    change allocated.globals = _
    rw [allocationGlobals]
    change markedPost.globals.update _ = _
    rw [markGlobals]
  have readyCode : ready.code = state.code := allocationCode.trans markCode
  have readyDomain : ready.memaddrs = state.memaddrs := allocationDomain.trans markDomain
  have readyMark : ready.locals.lookup (ofString "mark") = some (.val (.word pointer)) := by
    simp only [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    change allocated.locals.lookup (ofString "mark") = _
    rw [allocationLocals]
    simp [marked,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have readySource : ready.locals.lookup (ofString "s") = some (.val (.word pointer)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  refine Or.inl ⟨ready,⟨readyGlobals,readyCode,readyDomain,readyMark,readySource⟩,?_,?_,?_⟩
  · change state.clock ≤ allocated.clock + 2
    change allocated.clock = markedPost.clock - 1 at allocationClock
    omega
  · change allocated.clock ≤ state.clock
    change allocated.clock = markedPost.clock - 1 at allocationClock
    omega
  · rw [source_evmInit_temporary_mark,markDeclaration]
    dsimp only
    rw [source_evmInit_temporary_allocation,allocationDeclaration]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Reach the original heap-release call within two ticks, or reject at one
of the 33 literal stores. The saved mark and source pointer remain linked. -/
theorem evaluate_evmInit_temporary_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 40 ≤ 33806089496)
    (budget : 2 ≤ state.clock) :
    Reaches state (evmInitAt 0) (EvmTemporaryReady state pointer) 2 (evmInitAt 35) := by
  have declarations := evaluate_evmInit_temporary_declarations state pointer code heap aligned small budget
  exact reaches_trans state (evmInitAt 0) (evmInitAt 2) (evmInitAt 35)
    (EvmTemporaryReady state pointer) (EvmTemporaryReady state pointer) 2 0 declarations
    (by
      intro middle valid
      exact reaches_mono middle (evmInitAt 2) (evmInitAt 35) (ByteStoreControlFrame middle)
        (EvmTemporaryReady state pointer) 0 0 (by omega)
        (by
          intro next frame
          exact ⟨frame.1.trans valid.1,frame.2.2.1.trans valid.2.1,
            frame.2.2.2.trans valid.2.2.1,by rw [frame.2.1]; exact valid.2.2.2.1,
            by rw [frame.2.1]; exact valid.2.2.2.2⟩)
        (evaluate_evmInit_literal_stores_reaches middle))

#print axioms evaluate_evmInit_temporary_declarations
#print axioms evaluate_evmInit_temporary_prefix
end InitECandidate.Runtime

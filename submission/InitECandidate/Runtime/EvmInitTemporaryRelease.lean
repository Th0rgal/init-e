import InitECandidate.Runtime.EvmInitTemporaryPrefix
import InitECandidate.Runtime.HeapReleaseCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def EvmTemporaryReleased {F : Type} (initial : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = initial.globals ∧ next.code = initial.code ∧ next.memaddrs = initial.memaddrs ∧
    next.locals.lookup (ofString "s") = some (.val (.word pointer))

theorem evaluate_evmInit_temporary_release_prefix {F : Type}
    (initial state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (code : initial.code = originalRuntimeCode)
    (heap : initial.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ready : EvmTemporaryReady initial pointer state) (budget : 1 ≤ state.clock) :
    Reaches state (evmInitAt 35) (EvmTemporaryReleased initial pointer) 1 (evmInitAt 36) := by
  have currentHeap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd pointer 40))) := by
    rw [ready.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "mark")] = some [.val (.word pointer)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ready.2.2.2.1]
  obtain ⟨next,run,clock,_,globals,locals,installed,domain,_⟩ :=
    evaluate_heapRelease_call state (.var .local (ofString "mark")) pointer (allocationEnd pointer 40)
      (ready.2.1.trans code) args currentHeap (by omega)
  have restored : next.globals = initial.globals := by
    rw [globals]
    change state.globals.update (ofString "heap_ptr",.val (.word pointer)) = _
    rw [ready.1]
    apply HolFiniteMapExact.ext
    funext key
    by_cases atHeap : key = ofString "heap_ptr"
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,heap]
    · simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm atHeap]
  rw [source_evmInit_temporary_release]
  apply reaches_seq
  exact Or.inl ⟨next,⟨restored,installed.trans ready.2.1,domain.trans ready.2.2.1,
    by rw [locals]; exact ready.2.2.2.2⟩,by omega,by omega,run⟩

/-- Temporary allocation and release spend three ticks in total. On the
normal path the frontier is exactly restored while the source pointer still
names the populated transfer-signature buffer. Early byte-store errors abort. -/
theorem evaluate_evmInit_temporary_released {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 40 ≤ 33806089496)
    (budget : 3 ≤ state.clock) :
    Reaches state (evmInitAt 0) (EvmTemporaryReleased state pointer) 3 (evmInitAt 36) := by
  have firstRun := evaluate_evmInit_temporary_prefix state pointer code heap aligned small (by omega)
  rcases firstRun with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · have release := evaluate_evmInit_temporary_release_prefix state middle pointer code heap valid (by omega)
    exact reaches_trans state (evmInitAt 0) (evmInitAt 35) (evmInitAt 36)
      (fun next => next = middle) (EvmTemporaryReleased state pointer) 2 1
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact release)
  · exact Or.inr (stAbort_mono state _ 2 3 (by omega) aborted)

#print axioms evaluate_evmInit_temporary_release_prefix
#print axioms evaluate_evmInit_temporary_released
end InitECandidate.Runtime

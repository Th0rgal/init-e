import InitECandidate.Runtime.StateRestoreRank
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Globals other than the allocator frontier have their caller values. -/
def HeapGlobalsFrame {F : Type} (before after : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ name, name ≠ ofString "heap_ptr" → after.globals.lookup name = before.globals.lookup name

theorem HeapGlobalsFrame.refl {F : Type} (state : PanSemStateFiniteExact 64 F) : HeapGlobalsFrame state state := by
  intro _ _; rfl

theorem HeapGlobalsFrame.trans {F : Type} {first middle last : PanSemStateFiniteExact 64 F}
    (one : HeapGlobalsFrame first middle) (two : HeapGlobalsFrame middle last) : HeapGlobalsFrame first last := by
  intro name different
  exact (two name different).trans (one name different)

theorem HeapGlobalsFrame.of_globals {F : Type} {before after : PanSemStateFiniteExact 64 F}
    (same : after.globals = before.globals) : HeapGlobalsFrame before after := by
  intro name _; rw [same]

theorem HeapGlobalsFrame.heap_update {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) :
    HeapGlobalsFrame state (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word pointer)) state) := by
  intro name different
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

/-- Heap allocation cannot change the remaining journal rank when caller locals are restored. -/
theorem HeapGlobalsFrame.restore_rank {F : Type} {before after : PanSemStateFiniteExact 64 F}
    (frame : HeapGlobalsFrame before after) (locals : after.locals = before.locals) :
    stateRestoreRank after = stateRestoreRank before := by
  have counter := frame (ofString "journal_n") (by decide)
  simp only [stateRestoreRank,counter,locals]

/-- The exact successful allocator call satisfies the non-heap-global frame. -/
theorem evaluate_alloc_call_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HeapGlobalsFrame state post ∧ post.locals = state.locals ∧ stateRestoreRank post = stateRestoreRank state := by
  obtain ⟨post,run,_,_,locals,_,_,_,_,globals,_⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments code clock heap request finish
  have frame : HeapGlobalsFrame state post := by
    intro name different
    rw [globals]
    exact HeapGlobalsFrame.heap_update state (allocationEnd pointer size) name different
  exact ⟨post,run,frame,locals,frame.restore_rank locals⟩

#print axioms HeapGlobalsFrame.trans
#print axioms HeapGlobalsFrame.restore_rank
#print axioms evaluate_alloc_call_heap_frame
end InitECandidate.Runtime

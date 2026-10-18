import InitECandidate.Runtime.AllocationGlobalCall
import InitECandidate.Runtime.AllocationPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def globalAllocationProgram : List (MlS × BitVec 64) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | (name,size) :: rest, tail =>
      .seq (.call (some (some (.global,name),none)) (ofString "alloc") [.const size])
        (globalAllocationProgram rest tail)

def globalAllocationGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) : List (MlS × BitVec 64) → HolFiniteMapExact MlS (ValueHOL 64)
  | [] => globals
  | (name,size) :: rest => globalAllocationGlobals
      ((globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer size)))).update
        (name,.val (.word pointer))) (allocationEnd pointer size) rest

theorem globalAllocationGlobals_lookup_other (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) (entries : List (MlS × BitVec 64)) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (absent : ∀ entry ∈ entries, key ≠ entry.1) :
    (globalAllocationGlobals globals pointer entries).lookup key = globals.lookup key := by
  induction entries generalizing globals pointer with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name,size⟩ := entry
    rw [globalAllocationGlobals,ih _ _ (fun entry member => absent entry (by simp [member]))]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,
      Ne.symm (absent (name,size) (by simp))]

/-- Execute an initializer's actual global allocator calls. The continuation
receives the computed globals and heap frontier; its execution is unrestricted.
Safe plans are consumed one allocation at a time. -/
theorem evaluate_globalAllocation_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (entries : List (MlS × BitVec 64)) (tail : ProgHOL 64) (pointer : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (names : ∀ entry ∈ entries, entry.1 ≠ ofString "heap_ptr")
    (words : ∀ entry ∈ entries, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (entries.map Prod.snd))
    (budget : entries.length ≤ state.clock) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (globalAllocationProgram entries tail) = evaluateHOLFiniteState ready tail ∧
      ready.clock = state.clock - entries.length ∧ ready.memory = state.memory ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals = globalAllocationGlobals state.globals pointer entries ∧
      ready.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (entries.map Prod.snd)))) := by
  induction entries generalizing state pointer with
  | nil => exact ⟨state,rfl,by simp,rfl,rfl,rfl,rfl,rfl,heap⟩
  | cons entry rest ih =>
    obtain ⟨name,size⟩ := entry
    have safeParts : size ≤ (33806089496 : BitVec 64) - pointer ∧
        (allocationEnd pointer size).toNat ≤ 33806089496 ∧
        AllocationPlanSafe (allocationEnd pointer size) (rest.map Prod.snd) := safe
    obtain ⟨old,present⟩ := words (name,size) (by simp)
    have different := names (name,size) (by simp)
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.const size] = some [.val (.word size)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
    obtain ⟨middle,call,ticks,memory,locals,installed,domain,_,assigned,nextHeap,other⟩ :=
      evaluate_alloc_global_call state (.const size) pointer size old name args code (by simp only [List.length_cons] at budget; omega)
        heap present different safeParts.1 safeParts.2.1
    have globals : middle.globals =
        (state.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer size)))).update
          (name,.val (.word pointer)) := by
      apply HolFiniteMapExact.ext
      funext key
      by_cases atName : key = name
      · subst key
        simpa [HolFiniteMapExact.lookup_update,FUPDATE] using assigned
      · by_cases atHeap : key = ofString "heap_ptr"
        · subst key
          simpa [HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm atName] using nextHeap
        · simpa [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm atName,Ne.symm atHeap] using other key atName atHeap
    have tailWords : ∀ entry ∈ rest, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      by_cases same : entry.1 = name
      · exact ⟨pointer,by rw [same]; exact assigned⟩
      · obtain ⟨word,wordAt⟩ := words entry (by simp [member])
        exact ⟨word,(other entry.1 same (names entry (by simp [member]))).trans wordAt⟩
    obtain ⟨ready,run,clock,retMemory,retLocals,retCode,retDomain,retGlobals,retHeap⟩ :=
      ih middle (allocationEnd pointer size) (installed.trans code) nextHeap
        (fun entry member => names entry (by simp [member])) tailWords safeParts.2.2
        (by simp only [List.length_cons] at budget; omega)
    refine ⟨ready,?_,?_,retMemory.trans memory,retLocals.trans locals,retCode.trans installed,
      retDomain.trans domain,?_,retHeap⟩
    · rw [globalAllocationProgram,evaluateHOLFiniteState_seq_line780,call]
      exact run
    · simp only [List.length_cons]
      omega
    · rw [retGlobals,globals]
      rfl

#print axioms evaluate_globalAllocation_prefix
#print axioms globalAllocationGlobals_lookup_other

theorem evaluate_globalAllocation_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (entries : List (MlS × BitVec 64)) (pointer : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (names : ∀ entry ∈ entries, entry.1 ≠ ofString "heap_ptr")
    (words : ∀ entry ∈ entries, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (entries.map Prod.snd))
    (budget : entries.length ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (globalAllocationProgram entries (.return (.const 0))) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - entries.length ∧ post.memory = state.memory ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer entries ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (entries.map Prod.snd)))) := by
  obtain ⟨ready,run,clock,memory,_,installed,domain,globals,finalHeap⟩ :=
    evaluate_globalAllocation_prefix state entries (.return (.const 0)) pointer code heap names words safe budget
  refine ⟨emptyLocalsHOLFinite ready,?_,clock,memory,rfl,installed,domain,globals,finalHeap⟩
  rw [run]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms evaluate_globalAllocation_return
end InitECandidate.Runtime

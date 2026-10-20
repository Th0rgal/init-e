import InitECandidate.Runtime.StateInitTableCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- All outcomes bounded from a concrete aligned/capped heap word, no reserve. -/
def StateInitHeapBounded (program : ProgHOL 64) (cost : Nat) : Prop :=
 ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),s.code=originalRuntimeCode→StateInitHeapReady s→
 cost≤s.clock→RunBounded s program cost

/-- A store can fail, and a continuing store leaves the actual heap word intact. -/
theorem state_init_store_seq_bounded (address value : ExpHOL 64) {tail : ProgHOL 64} {cost : Nat}
 (bounded : StateInitHeapBounded tail cost) : StateInitHeapBounded (.seq (.store address value) tail) cost := by
 intro F s code heap budget
 suffices bound : RunBounded s (.seq (.store address value) tail) (0+cost) by simpa only [Nat.zero_add] using bound
 apply RunBounded.seq (a:=0) (b:=cost) (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega)) (by omega)
 intro post run installed ticks
 have frame := evaluate_avoidsGlobalAssignment (ofString "heap_ptr") (.store address value) rfl s
 rw [run] at frame
 have nextHeap : StateInitHeapReady post := by
  obtain ⟨p,h,al,cap⟩ := heap
  exact ⟨p,frame.trans h,al,cap⟩
 exact bounded post (installed.trans code) nextHeap ticks

/-- Real assignment-form allocator call followed by a heap-bounded suffix. -/
theorem state_init_alloc_seq_bounded (kind : VarKind) (name : MlS) (arguments : List (ExpHOL 64))
 (destination : kind=.local ∨ name≠ofString "heap_ptr") {tail : ProgHOL 64} {cost : Nat}
 (bounded : StateInitHeapBounded tail cost) :
 StateInitHeapBounded (.seq (.call (some (some (kind,name),none)) (ofString "alloc") arguments) tail) (2+cost) := by
 intro F s code heap budget
 apply RunBounded.seq (RunBounded.ofProg (ProgBounded.alloc _ _) code (by omega)) budget
 intro post run installed ticks
 have nextHeap := state_init_assignment_call_heap s post kind name (ofString "alloc") arguments
  _ _ _ originalRuntimeCode_allocation_lookup alloc_returnedRel destination code heap run
 exact bounded post (installed.trans code) nextHeap ticks

/-- Real fixed-capacity table call followed by a heap-bounded suffix. -/
theorem state_init_table_seq_bounded (name : MlS) (width capacity : BitVec 64)
 {tail : ProgHOL 64} {cost : Nat} (bounded : StateInitHeapBounded tail cost) :
 StateInitHeapBounded (.seq (.call (some (some (.local,name),none)) (ofString "htab_new")
 [.const width,.const capacity]) tail) (htabNewCost capacity+1+cost) := by
 intro F s code heap budget
 apply RunBounded.seq (runBounded_state_init_table_call s width capacity name code heap (by omega)) budget
 intro post run installed ticks
 have nextHeap := state_init_assignment_call_heap s post .local name (ofString "htab_new")
  [.const width,.const capacity] _ _ _ originalRuntimeCode_htabNew_lookup
  (NormalRel.returned htabNew_normalRel) (Or.inl rfl) code heap run
 exact bounded post (installed.trans code) nextHeap ticks
#print axioms state_init_store_seq_bounded
#print axioms state_init_alloc_seq_bounded
#print axioms state_init_table_seq_bounded
end InitECandidate.Runtime

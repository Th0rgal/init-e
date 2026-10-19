import InitECandidate.Runtime.CompactAfterAllocGlobals
import InitECandidate.Runtime.CompactNibbleAllocate
import InitECandidate.Runtime.CompactNibbleByteScope
import InitECandidate.Runtime.CompactNibbleEmptyBody
import InitECandidate.Runtime.CompactNibbleHeapWordFrame
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem compact_nibble_allocate_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleAllocate = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.const 2,.var .local (ofString "n")]] = some [.val (.word (2*length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
  rw [source_compactNibble_allocate] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "out")
      (.panop .mul [.const 2,.var .local (ofString "n")]) compactNibbleAfterAlloc heap (2*length) value
      args code atHeap heapBound run
  have kept := compact_after_alloc_global_frame ready (readyCode.trans code)
  rw [tailRun] at kept
  refine ⟨?_,by omega,within,aligned⟩
  rw [postGlobals,kept,globals]
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem compact_nibble_odd_scope_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleOddScope = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  rw [source_compactNibble_odd_scope] at run
  obtain ⟨iv,output,initialized,childRun,postEq⟩ := evaluate_dec_returned_scope s post
    (ofString "odd") _ _ _ value run
  have facts := compact_nibble_allocate_returned_heap
    (setVarHOLFinite (ofString "odd") iv s) output length heap
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "odd" ≠ ofString "n" by decide] using atLength)
    atHeap heapBound code value childRun
  rw [postEq]
  exact facts

theorem compact_nibble_leaf_scope_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleLeafScope = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  rw [source_compactNibble_leaf_scope] at run
  obtain ⟨iv,output,initialized,childRun,postEq⟩ := evaluate_dec_returned_scope s post
    (ofString "is_leaf") _ _ _ value run
  have facts := compact_nibble_odd_scope_returned_heap
    (setVarHOLFinite (ofString "is_leaf") iv s) output length heap
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "is_leaf" ≠ ofString "n" by decide] using atLength)
    atHeap heapBound code value childRun
  rw [postEq]
  exact facts

theorem compact_nibble_first_scope_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleFirstScope = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  rw [source_compactNibble_first_scope] at run
  obtain ⟨iv,output,initialized,childRun,postEq⟩ := evaluate_dec_returned_scope s post
    (ofString "first") _ _ _ value run
  have facts := compact_nibble_leaf_scope_returned_heap
    (setVarHOLFinite (ofString "first") iv s) output length heap
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "first" ≠ ofString "n" by decide] using atLength)
    atHeap heapBound code value childRun
  rw [postEq]
  exact facts

theorem compact_nibble_byte_scope_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleByteScope = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  rw [source_compactNibble_byte_scope] at run
  obtain ⟨iv,output,initialized,childRun,postEq⟩ := evaluate_dec_returned_scope s post
    (ofString "c0") _ _ _ value run
  have facts := compact_nibble_first_scope_returned_heap
    (setVarHOLFinite (ofString "c0") iv s) output length heap
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "c0" ≠ ofString "n" by decide] using atLength)
    atHeap heapBound code value childRun
  rw [postEq]
  exact facts

/-- The exact actual compact call retains a monotone capped aligned heap
frontier, derived from its returned allocation and no-global-write conversion. -/
theorem compact_nibble_body_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (length heap : BitVec 64)
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_compact_to_nibbles) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
      heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
      (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
      (allocationEnd heap (2*length)).toNat % 8 = 0 := by
  rw [source_compactNibble_body] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 5 code normal
  subst next
  exact compact_nibble_byte_scope_returned_heap s post length heap atLength atHeap heapBound code value tailRun

#print axioms compact_nibble_allocate_returned_heap
#print axioms compact_nibble_odd_scope_returned_heap
#print axioms compact_nibble_leaf_scope_returned_heap
#print axioms compact_nibble_first_scope_returned_heap
#print axioms compact_nibble_byte_scope_returned_heap
#print axioms compact_nibble_body_returned_heap_contract
end InitECandidate.Runtime

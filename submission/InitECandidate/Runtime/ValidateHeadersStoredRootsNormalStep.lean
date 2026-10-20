import InitECandidate.Runtime.ValidateHeadersStoredRootsBodyStep
import InitECandidate.Runtime.ValidateHeadersStoredRootsCallReach
import InitECandidate.Runtime.ValidateHeadersFirstPointerLoop
/-!
The complete actual first loop, carrying the stored parent records.

`ValidateHeadersStoredRootsInvariant` is the lead's `ValidateHeadersFirstPointerInvariant` (the
concrete runtime invariant, the typed index, the initialized pointer prefix and the frontier
bound that keeps the pointer buffer alive) together with the stored-record component:
`ValidateHeadersStoredRoots` at the loop's own index, bounded by the live heap, with the fixed
floor below the heap so that a later iteration can still separate a stored record from its writes.

The step theorem re-establishes all of it from one actual iteration.  It is the only place where
the decode call's contract, its reported window, its returned record and its tail are combined:
`validate_headers_parent_reaches` is applied with the caller's own table as the outer witness
prefix, `reaches_normal_continuation_budget` extracts the call's intermediate state, its remaining
budget and the scoped agreement between the whole body run and the tail run from that state, and
`validate_headers_stored_roots_body_step` does the carrying and the extension.

The heap room premise is the explicit interim invariant of the decode call: it says that the heap
at any state the loop starts an iteration in still has room for the largest header record
(`headerCarryRoom`, 624 bytes).  It is stated about the heap binding of the loop's state and stays
visible in every theorem of this module.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The full pointer invariant plus the stored parent records: the records below the loop's index
carry readable state root words, sit below the live heap and at or above the fixed floor, and the
floor itself is below the live heap. -/
def ValidateHeadersStoredRootsInvariant {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ValidateHeadersFirstPointerInvariant e s rank ∧
  ∃ index heap : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    e.hashes.toNat + e.count.toNat * 32 + 32 ≤ heap.toNat ∧
    ValidateHeadersStoredRoots s e.hs index.toNat heap.toNat (e.hashes.toNat + e.count.toNat * 32 + 32)

/-- A successful enabled actual iteration re-establishes the full invariant with the stored parent
records, with a strictly smaller natural rank. -/
theorem validate_headers_stored_roots_invariant_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (completeValid : ValidateHeadersStoredRootsInvariant e s rank)
    (code : s.code = originalRuntimeCode) (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (room : ∀ heap : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) →
      heap.toNat + headerCarryRoom ≤ 33806089496)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ValidateHeadersStoredRootsInvariant e post nextRank := by
  obtain ⟨valid,⟨prefixIndex,atPrefixIndex,initialized⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩ :=
    completeValid.1
  obtain ⟨index,heap,atIndex,heapGlobal,storedFloor,roots⟩ := completeValid.2
  obtain ⟨storedIndex,storedHeap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,
    scratch,frame,invHeapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have sameIndex : storedIndex = index := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (i.symm.trans atIndex)))
  have sameHeap : storedHeap = heap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (invHeapGlobal.symm.trans heapGlobal)))
  have withinIndex : index.toNat ≤ e.count.toNat := sameIndex ▸ within
  have iIndex : s.locals.lookup (ofString "i") = some (.val (.word index)) := sameIndex ▸ i
  have inputBeforeHeap : e.input.toNat + e.inputLength.toNat ≤ heap.toNat := sameHeap ▸ inputBefore
  have heapArenaHere : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address := fun address low high => heapArena address (by rw [sameHeap]; exact low) high
  have heapBoundHere : heap.toNat ≤ 33806089496 := sameHeap ▸ heapBound
  have tableBeforeHere : e.array.toNat + e.count.toNat * 16 ≤ heap.toNat := sameHeap ▸ tableBefore
  have inside := validate_headers_first_condition_enabled s index e.count w e.cap withinIndex iIndex n
    condition nonzero
  obtain ⟨pointer,length,entry⟩ := table index inside
  obtain ⟨finalHeap,finalHeapGlobal,heapMono,finalHeapBound,finalHeapAligned,scratchNext,frameNext,
    domain,installed,tableNext,workspace,increment⟩ :=
    validate_headers_first_body_normal_frame s post e.array e.count index pointer length e.input
      e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
      arr iIndex entry table e.inputBound e.inputAfter inputBeforeHeap e.tableAbove tableBeforeHere
      (by have := e.inputCap; omega) scratch frame code e.orderedFrame e.framePositive e.scratchBelow
      arena heapGlobal heapBoundHere (by have := e.inputCap; omega) heapArenaHere e.ceilingAligned hs hashes
      inside e.tableBeforeHs e.hsBufferBound e.hashBufferBound e.hashAligned e.inputCap state pad budget
      e.hsBeforeHashes e.stateBelow e.padBelow normal
  -- the decode call's contract, now a small named statement
  have heapCapped := room heap heapGlobal
  have reached := validate_headers_stored_roots_parent_reaches s e.array heap index pointer length
    e.input e.inputLength e.scratch e.frame e.count e.ceiling e.inputLimit arr iIndex entry
    entry.noWrap ((entry.length_bound s e.array index pointer length e.input e.inputLength).trans e.inputBound)
    (by have := e.inputCap; omega) scratch frame code e.orderedFrame e.framePositive e.scratchBelow
    arena heapGlobal heapCapped (by have := e.inputCap; omega) heapArenaHere e.ceilingAligned
    (e.inputAfter.trans entry.startsWithin) (by have := entry.endsWithin; omega) table e.tableAbove
    tableBeforeHere (by omega)
  obtain ⟨mid,carried,midBudget,linked,tailNormal⟩ :=
    reaches_normal_continuation_budget s validateHeadersFirstBody validateHeadersFirstTail
      (StoredRootsParentCarry s heap pointer length e.ceiling e.array e.input e.inputLength e.count)
      (headerDecoderBodyCost e.inputLimit + 1) (e.inputLimit * 20 + 125) reached budget
      (by rw [normal])
  -- one complete iteration, from the entry state through the call and its tail
  obtain ⟨record,nextHeap,atRecord,postHeap,rootsNext,growth⟩ :=
    validate_headers_stored_roots_body_step s mid post e.array e.count index pointer length e.input
      e.inputLength e.hs e.hashes e.keccakState e.keccakPad heap e.array e.input e.inputLength e.count e.inputLimit e.ceiling
      heap.toNat roots carried linked inside code rfl heapBoundHere heapCapped
      (by have := e.tableAbove; have := tableBeforeHere; omega) arr iIndex hs hashes table
      e.tableAbove e.tableBeforeHs bufferBeforeHashes storedFloor (Nat.le_trans e.stateBelow hsAbove)
      (Nat.le_trans e.padBelow hsAbove) e.hsBufferBound
      e.hashBufferBound e.hashAligned e.inputBound (by have := e.inputCap; omega) state pad e.stateBelow
      e.padBelow midBudget normal
  have sameNextHeap : nextHeap = finalHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (postHeap.symm.trans finalHeapGlobal)))
  have nextFloorHere : e.hashes.toNat + e.count.toNat * 32 + 32 ≤ nextHeap.toNat := by
    rw [sameNextHeap]
    omega
  obtain ⟨nextRank,smaller,pointerNext⟩ :=
    validate_headers_first_pointer_invariant_step e s post rank hsAbove bufferBeforeHashes completeValid.1
      code w condition nonzero budget normal
  have indexNat : (index + 1).toNat = index.toNat + 1 := (validate_headers_index_progress index e.count
    inside).1
  exact ⟨nextRank,smaller,pointerNext,⟨index + 1,nextHeap,increment,postHeap,nextFloorHere,by
    rw [indexNat]
    exact rootsNext⟩⟩

#print axioms validate_headers_stored_roots_invariant_step
end InitECandidate.Runtime

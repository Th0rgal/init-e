import InitECandidate.Runtime.ValidateHeadersStoredRootsIteration
import InitECandidate.Runtime.ValidateHeadersCarryHeapRoom
import InitECandidate.Runtime.ValidateHeadersParentCarryWorkspace
import InitECandidate.Runtime.ValidateHeadersFirstTailStoreCell
import InitECandidate.Runtime.ReachesNormalContinuation
/-!
One complete actual validation iteration keeps every stored parent record - through the decode
body, through that call's tail, and including the record this iteration decoded.

This is the composition the loop's invariant needs, in the order the run has:

1. `parentRecordCarry` is the decode call's contract: the actual returned record `record`, its
   generated state root word at `record + 32`, the memory domain, the code, the new heap and the
   words of `[ceiling, heapStart)`.
2. `ValidateHeadersStoredRoots.after_window` carries the older records across the decode body:
   both their pointer cells (`hs + slot * 8`, below the hash buffer) and their root words (below
   `heapStart`, because their 248-byte extents end below the live frontier) lie in the window the
   call reports.
3. `validate_headers_first_tail_stored_roots_geometry` carries them across the actual tail, with
   the separation derived from the buffer layout rather than assumed.
4. `validate_headers_first_tail_store_cell` and `validate_headers_first_tail_single_word` say that
   the tail leaves the new record in its slot and does not disturb the new record's root word.
5. `validateHeadersStoredRoots_store` adds the new record, bounded by the heap the iteration
   allocated.

The frontier of the component is the live heap, so it moves with the allocation; the floor is the
fixed end of the hash buffer, so it does not.  The heap room premise of the loop's decode call
(`headerCarryRoom`, 624 bytes) enters only through `parentRecordCarry`, where it stays visible.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- One complete actual validation iteration, from the loop entry state through the decode call
and its tail to the closure state, keeps every stored parent record and adds the record it
decoded: the returned record sits in its own slot with its readable root word, and the next live
frontier is the heap after the record's state-root allocation. -/
theorem validate_headers_stored_roots_body_step {F : Type}
    (s mid post : PanSemStateFiniteExact 64 F)
    (array count index pointer length input inputLength hs hashes keccakState keccakPad
      heapStart : BitVec 64)
    (older outerInput outerLength olderCount : BitVec 64)
    (inputLimit ceiling frontier : Nat)
    (roots : ValidateHeadersStoredRoots s hs index.toNat frontier (hashes.toNat + count.toNat * 32 + 32))
    (carried : parentRecordCarry s mid heapStart pointer length ceiling older outerInput outerLength olderCount)
    (linked : Scoped (evaluateHOLFiniteState s validateHeadersFirstBody)
      (evaluateHOLFiniteState mid validateHeadersFirstTail))
    (inside : index.toNat < count.toNat) (code : s.code = originalRuntimeCode)
    (frontierAtHeap : frontier = heapStart.toNat) (frontierBound : frontier ≤ 33806089496)
    (heapCapped : heapStart.toNat + headerCarryRoom ≤ 33806089496)
    (ceilingBelowHeap : ceiling ≤ heapStart.toNat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (tableAbove : ceiling ≤ array.toNat) (tableBefore : array.toNat + count.toNat * 16 ≤ hs.toNat)
    (bufferBeforeHashes : hs.toNat + count.toNat * 8 ≤ hashes.toNat)
    (floorBelowHeap : hashes.toNat + count.toNat * 32 + 32 ≤ heapStart.toNat)
    (stateBeforeHs : keccakState.toNat + 200 ≤ hs.toNat)
    (padBeforeHs : keccakPad.toNat + 136 ≤ hs.toNat)
    (hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (midBudget : inputLimit * 20 + 125 ≤ mid.clock)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ record finalHeap : BitVec 64,
      mid.locals.lookup (ofString "h") = some (.val (.word record)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      ValidateHeadersStoredRoots post hs (index.toNat + 1) finalHeap.toNat
        (hashes.toNat + count.toNat * 32 + 32) ∧
      finalHeap.toNat < heapStart.toNat + headerCarryRoom := by
  have carriedKeep := carried
  obtain ⟨value,dbody,dcount,drecord,drooted,decodeRun,decodeShape,valueEq,recordEq,nextEq,hLocal,
    rootWord,rootDomain,domain,codeHere,heapPost,scratchPost,framePost,before,room,window,outer⟩ :=
    carried
  -- the tail that runs inside the same call
  have tailNormal : (evaluateHOLFiniteState mid validateHeadersFirstTail).1 = none := by
    have same := linked.1
    rw [normal] at same
    exact same.symm
  let tailPost := (evaluateHOLFiniteState mid validateHeadersFirstTail).2
  have tailRun : evaluateHOLFiniteState mid validateHeadersFirstTail = (none,tailPost) :=
    Prod.ext tailNormal rfl
  have memoryPost : post.memory = tailPost.memory := by
    have same := linked.2.2.1
    rw [normal] at same
    exact same
  have globalsPost : post.globals = tailPost.globals := by
    have same := linked.2.2.2.1
    rw [normal] at same
    exact same
  have domainPost : post.memaddrs = tailPost.memaddrs := by
    have same := linked.2.2.2.2
    rw [normal] at same
    exact same
  -- what the call hands the tail
  have midArray : mid.locals.lookup (ofString "arr") = some (.val (.word array)) :=
    (parent_record_carry_locals s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount carriedKeep (ofString "arr") (by decide)).trans atArray
  have midIndex : mid.locals.lookup (ofString "i") = some (.val (.word index)) :=
    (parent_record_carry_locals s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount carriedKeep (ofString "i") (by decide)).trans atIndex
  have midHs : mid.locals.lookup (ofString "hs") = some (.val (.word hs)) :=
    (parent_record_carry_locals s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount carriedKeep (ofString "hs") (by decide)).trans atHs
  have midHashes : mid.locals.lookup (ofString "hashes") = some (.val (.word hashes)) :=
    (parent_record_carry_locals s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount carriedKeep (ofString "hashes") (by decide)).trans atHashes
  have midTable : RlpSliceInputPrefix mid array input inputLength count.toNat :=
    parent_record_carry_table s mid heapStart pointer length ceiling older outerInput outerLength olderCount
      array count input inputLength carriedKeep table tableAbove (by omega)
  have midState : mid.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) :=
    (parent_record_carry_workspace s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount code carriedKeep (ofString "keccak_st") (by exact List.Mem.head _)).trans stateGlobal
  have midPad : mid.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) :=
    (parent_record_carry_workspace s mid heapStart pointer length ceiling older outerInput outerLength
      olderCount code carriedKeep (ofString "keccak_pad") (by exact List.Mem.tail _ (List.Mem.head _))).trans padGlobal
  have midCode : mid.code = originalRuntimeCode := codeHere.trans code
  -- the floor and the geometry of the buffers
  have hsAbove : ceiling ≤ hs.toNat := by omega
  have hsBeforeHashes : hs.toNat ≤ hashes.toNat := by omega
  have floorAbove : ceiling ≤ hashes.toNat + count.toNat * 32 + 32 := by omega
  have bufferBeforeFloor : hs.toNat + count.toNat * 8 ≤ hashes.toNat + count.toNat * 32 + 32 := by omega
  have floorBeforeHeap : hs.toNat + count.toNat * 8 ≤ heapStart.toNat := by omega
  have heapBeforeRecord : heapStart.toNat ≤ drecord.toNat := by omega
  -- step 2: the decode body keeps every older record
  have rootsMid : ValidateHeadersStoredRoots mid hs index.toNat frontier
      (hashes.toNat + count.toNat * 32 + 32) := by
    refine ValidateHeadersStoredRoots.after_window s mid hs index.toNat frontier
      (hashes.toNat + count.toNat * 32 + 32) ceiling heapStart.toNat roots domain window ?_ ?_ floorAbove
    · intro slot within
      have slotProduct : (slot * (8#64)).toNat = slot.toNat * 8 := by
        rw [BitVec.toNat_mul_of_lt (by change slot.toNat * 8 < 2^64; omega)]
        rfl
      have slotAddr : (hs + slot * (8#64)).toNat = hs.toNat + slot.toNat * 8 := by
        rw [BitVec.toNat_add_of_lt (by rw [slotProduct]; omega),slotProduct]
      rw [slotAddr]
      constructor <;> omega
    · intro prior aboveFloor extent
      have rootAddr : (prior + 32#64).toNat = prior.toNat + 32 := by
        rw [BitVec.toNat_add_of_lt (by change prior.toNat + 32 < 2^64; omega)]
        rfl
      rw [rootAddr,← frontierAtHeap]
      constructor <;> omega
  have tailFrame := validate_headers_first_tail_normal_frame mid tailPost array count index input
    inputLength hs hashes drecord keccakState keccakPad inputLimit ceiling midArray midIndex midHs
    midHashes hLocal inside midTable (by omega) hsBufferBound hashBufferBound hashAligned inputBound
    limitBound midState midPad midCode midBudget tableAbove hsBeforeHashes stateBelow padBelow tailRun
  obtain ⟨tailTable,tailLocals,tailGlobals,tailDomain,tailCode,tailMemory,tailProgress⟩ := tailFrame
  -- step 3: the actual tail keeps every older record
  have rootsTail : ValidateHeadersStoredRoots tailPost hs index.toNat frontier
      (hashes.toNat + count.toNat * 32 + 32) := by
    refine validate_headers_first_tail_stored_roots_geometry mid tailPost array count index input inputLength
      hs hashes drecord keccakState keccakPad inputLimit ceiling index.toNat frontier rootsMid tailDomain
      inside (by omega) (le_refl index.toNat) bufferBeforeHashes stateBeforeHs padBeforeHs hsBufferBound
      hashBufferBound hashAligned frontierBound midArray midIndex midHs midHashes hLocal midTable
      (by omega) inputBound limitBound midState midPad midCode midBudget tableAbove hsBeforeHashes
      stateBelow padBelow tailRun
  have rootsPost : ValidateHeadersStoredRoots post hs index.toNat frontier
      (hashes.toNat + count.toNat * 32 + 32) := by
    unfold ValidateHeadersStoredRoots at rootsTail ⊢
    rw [memoryPost,domainPost]
    exact rootsTail
  -- the tail's own frames: the new record's root word and its slot
  have outside := validate_headers_tail_root_outside mid hs hashes index count keccakState keccakPad
    drecord heapStart ceiling inside (by omega) floorBelowHeap heapBeforeRecord room ceilingBelowHeap
    stateBelow padBelow hashAligned
  have keptRoot := validate_headers_first_tail_single_word mid tailPost array count index input inputLength
    hs hashes drecord keccakState keccakPad (drecord + 32#64) inputLimit ceiling midArray midIndex midHs
    midHashes hLocal inside midTable (by omega) hsBufferBound hashBufferBound hashAligned inputBound
    limitBound midState midPad midCode midBudget tableAbove hsBeforeHashes stateBelow padBelow
    outside.2.2.2 outside.1 outside.2.1 outside.2.2.1 tailRun
  have storeOutside := validate_headers_tail_store_outside hs hashes index count keccakState keccakPad
    inside bufferBeforeHashes stateBeforeHs padBeforeHs hsBufferBound hashAligned hashBufferBound
  have storedCell := validate_headers_first_tail_store_cell mid tailPost array count index input inputLength
    hs hashes drecord keccakState keccakPad inputLimit ceiling midArray midIndex midHs midHashes hLocal
    inside midTable (by omega) hsBufferBound hashBufferBound hashAligned inputBound limitBound midState
    midPad midCode midBudget tableAbove hsBeforeHashes stateBelow padBelow storeOutside.1
    storeOutside.2.1 storeOutside.2.2 tailRun
  -- the heap after the record's state-root allocation
  let finalHeap := allocationEnd drecord 248
  have sizeBound : drecord.toNat + (248 : BitVec 64).toNat ≤ 33806089496 := by
    have same : (248 : BitVec 64).toNat = 248 := rfl
    rw [same]
    exact room
  have finalHeapExtent : drecord.toNat + 248 ≤ finalHeap.toNat :=
    (allocationEnd_covers drecord 248 sizeBound).1
  have tailHeap : tailPost.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) := by
    show tailPost.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd drecord 248)))
    rw [recordEq,tailGlobals]
    exact heapPost
  have postHeap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) := by
    rw [globalsPost]
    exact tailHeap
  have fits : index.toNat * 8 < 2^64 := by omega
  have finalBelow : frontier ≤ finalHeap.toNat := by omega
  have aboveFloor : hashes.toNat + count.toNat * 32 + 32 ≤ drecord.toNat := by omega
  have storeCell : post.memory (hs + index * (8#64)) = .word drecord :=
    (congrFun memoryPost (hs + index * (8#64))).trans storedCell
  have storeRoot : post.memory (drecord + 32#64) = .word drooted :=
    (congrFun memoryPost (drecord + 32#64)).trans (keptRoot.1.trans rootWord)
  have storeDomain : post.memaddrs (drecord + 32#64) :=
    (domainPost.trans tailDomain).symm ▸ rootDomain
  refine ⟨drecord,finalHeap,hLocal,postHeap,?_,?_⟩
  exact validateHeadersStoredRoots_store post post hs index drecord drooted finalHeap.toNat
    (hashes.toNat + count.toNat * 32 + 32)
    (ValidateHeadersStoredRoots.mono post hs index.toNat frontier finalHeap.toNat
      (hashes.toNat + count.toNat * 32 + 32) finalBelow rootsPost)
    fits rfl storeCell storeRoot storeDomain finalHeapExtent aboveFloor
    (fun (slot : BitVec 64) (_ : slot.toNat < index.toNat) => rfl)
    (fun (slot : BitVec 64) (_ : slot.toNat < index.toNat) (prior : BitVec 64)
      (_ : post.memory (hs + slot * (8#64)) = .word prior) (word : BitVec 64)
      (rooted : post.memory (prior + 32#64) = .word word) => rooted)
  · -- the iteration's growth, both bindings being the same allocation term
    obtain ⟨roomRecord,roomLocal,carryHeap,carryBinding,carryBound⟩ :=
      validate_headers_carry_heap_room s mid heapStart pointer length ceiling older outerInput
        outerLength olderCount heapCapped carriedKeep
    have midCarry : carryHeap = allocationEnd (allocationEnd heapStart (dcount * 16)) 248 := by
      exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (carryBinding.symm.trans heapPost)))
    have tailAt := (congrArg (fun g => g.lookup (ofString "heap_ptr")) globalsPost).symm.trans postHeap
    have same : finalHeap = carryHeap := by
      rw [show finalHeap = allocationEnd (allocationEnd heapStart (dcount * 16)) 248 from by
        rw [show finalHeap = allocationEnd drecord 248 from rfl, recordEq], midCarry]
    rw [same]
    exact carryBound

#print axioms validate_headers_stored_roots_body_step
end InitECandidate.Runtime

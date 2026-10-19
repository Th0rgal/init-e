import InitECandidate.Runtime.RunAttemptHeadersDeclarationReach
import InitECandidate.Runtime.ValidateHeadersBodyReturnedContract
/-!
The actual `run_attempt` header-validation declaration, carried through the real
original callee run.

Root's `run_attempt_headers_declaration_reaches` keeps the returned body run but
only records that the caller local `vh` receives the returned value.  Here the
checked contract of the whole original `validate_headers` body is applied to that
retained run, so the reached `runAttemptAt 3` state also carries the exact
`(hs, hashes)` pair, the header count cap, the monotone aligned live allocation
frontier, the caller workspace pointers, the untouched older memory window and
the retained original witness prefix.  No new caller assumption is introduced:
the reach is strengthened in place at the same cost.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual `run_attempt` declaration reaches its real continuation while
carrying the complete returned contract of the original validating callee. -/
theorem run_attempt_headers_declaration_contract {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 2)
      (fun ready => ∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (validateHeadersCallee array count))
          (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned value),bodyPost) ∧
        ready.locals = s.locals.update (ofString "vh",value) ∧
        ready.memory = bodyPost.memory ∧ ready.globals = bodyPost.globals ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        value = .rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))] ∧
        ready.locals.lookup (ofString "vh") =
          some (.rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))]) ∧
        count.toNat ≤ 256 ∧
        (∃ finalHeap : BitVec 64,
          ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
          (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
            bodyPost.memaddrs address)) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
          ready.memory address = s.memory address) ∧
        RlpSliceInputPrefix bodyPost array input inputLength count.toNat ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat)
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 3) := by
  have reached := run_attempt_headers_declaration_reaches s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal
    stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget
  refine reaches_mono s (runAttemptAt 2) (runAttemptAt 3) _ _ _ _ (le_refl _) ?_ reached
  intro ready facts
  obtain ⟨value,bodyPost,bodyRun,pinLocal,memoryEq,globalsEq,domainEq,codeEq⟩ := facts
  obtain ⟨atArray,atCount,table,arrayEnd,countBound⟩ :=
    run_attempt_headers_entry s si array count input inputLength heap linked
  have contract := validate_headers_body_returned_contract
    (callEntryStateHOLFinite s (validateHeadersCallee array count)) bodyPost array count input inputLength scratch
    frame heap keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove arrayEnd
    inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray atCount table
    scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by change validateHeadersBodyCost inputLimit ≤ s.clock - 1; omega) value bodyRun
  obtain ⟨countCap,⟨finalHeap,atFrontier,frontierLower,frontierBound,frontierAligned,frontierArena⟩,
    scratchPost,framePost,statePost,padPost,windowPost,tablePost,codePost,valueIs⟩ := contract
  have vhLocal : ready.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))]) := by
    rw [pinLocal,valueIs]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  have cellValue : ∀ index : BitVec 64, index.toNat < count.toNat →
      (array + index * 16#64).toNat = array.toNat + index.toNat * 16 := by
    intro index small
    have sixteen : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [BitVec.toNat_add,BitVec.toNat_mul,sixteen]
    rw [Nat.mod_eq_of_lt (by omega : index.toNat * 16 < 2 ^ 64)]
    rw [Nat.mod_eq_of_lt (by omega : array.toNat + index.toNat * 16 < 2 ^ 64)]
  have endValue : ∀ index : BitVec 64, index.toNat < count.toNat →
      (array + index * 16#64 + 8#64).toNat = array.toNat + index.toNat * 16 + 8 := by
    intro index small
    have eight : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [BitVec.toNat_add,cellValue index small,eight]
    rw [Nat.mod_eq_of_lt (by omega : array.toNat + index.toNat * 16 + 8 < 2 ^ 64)]
  have prefixReady : RlpSliceInputPrefix ready array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨pointer,length,source⟩ := linked.slices slot inside
    refine ⟨pointer,length,RlpSliceInputEntry.after_frame s ready array slot pointer length input inputLength source
      domainEq ?_ ?_⟩
    · rw [memoryEq]
      exact windowPost _ (by rw [cellValue slot inside]; omega) (by rw [cellValue slot inside]; omega)
    · rw [memoryEq]
      exact windowPost _ (by rw [endValue slot inside]; omega) (by rw [endValue slot inside]; omega)
  exact ⟨value,bodyPost,bodyRun,pinLocal,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,countCap,
    ⟨finalHeap,(by rw [globalsEq]; exact atFrontier),frontierLower,frontierBound,frontierAligned,
      frontierArena⟩,
    (by rw [globalsEq]; exact scratchPost),(by rw [globalsEq]; exact framePost),
    (by rw [globalsEq]; exact statePost),(by rw [globalsEq]; exact padPost),
    (by intro address low high; rw [memoryEq]; exact windowPost address low high),tablePost,prefixReady⟩

#print axioms run_attempt_headers_declaration_contract
end InitECandidate.Runtime

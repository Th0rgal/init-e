import InitECandidate.Runtime.RunAttemptEntryTransactionChecksMemory
import InitECandidate.Runtime.RunAttemptZeroHeaderEntryTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- The actual entry-to-transaction-check prefix also covers an empty header
array at address zero: that path terminates before any parent or database access. -/
theorem run_attempt_entry_transaction_checks_memory_all_headers {F : Type}
 (s : PanSemStateFiniteExact 64 F)
 (si payload array count inputLength heap keccakState keccakPad stateArray stateCount codeArray codeCount output oldWs emptyRoot : BitVec 64)
 (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
 (siCell : s.memory (si+0#64)=.word payload)
 (inputSmall : inputLength.toNat≤134217712)
 (inputBefore : 2713731432+inputLength.toNat≤heap.toNat)
 (tableOrigin : count=0 ∨ 2713731432≤array.toNat)
 (linked : WitnessArrayLinked s si 72 80 array count (2713731432#64) inputLength heap)
 (stateLinked : WitnessArrayLinked s si 40 48 stateArray stateCount (2713731432#64) inputLength heap)
 (stateArrayAbove : stateCount.toNat=0 ∨ 2713731432≤stateArray.toNat)
 (codeLinked : WitnessArrayLinked s si 56 64 codeArray codeCount (2713731432#64) inputLength heap)
 (codeArrayAbove : codeCount.toNat=0 ∨ 2713731432≤codeArray.toNat)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))))
 (stateGlobal : s.globals.lookup (ofString "keccak_st")=some (.val (.word keccakState)))
 (padGlobal : s.globals.lookup (ofString "keccak_pad")=some (.val (.word keccakPad)))
 (outputGlobal : s.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word output)))
 (wsGlobal : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (emptyGlobal : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (stateBelow : keccakState.toNat+200≤2713731432) (padBelow : keccakPad.toNat+136≤2713731432)
 (outputBelow : output.toNat+32≤2713731432) (outputAligned : output.toNat%8=0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (heapGlobal : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapUpper : heap.toNat≤33805910000) (code : s.code=originalRuntimeCode)
 (recordAbove : 2713731432≤si.toNat) (recordBefore : si.toNat+88≤heap.toNat)
 (budget : runAttemptEntryTransactionChecksCost≤s.clock) :
 Reaches s (runAttemptAt 0)
  (fun post=>StateInitHeapReady post ∧post.code=originalRuntimeCode ∧post.memaddrs=s.memaddrs ∧
   post.locals.lookup (ofString "si")=some (.val (.word si)) ∧
   post.locals.lookup (ofString "pl")=some (.val (.word payload)) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<heap.toNat→post.memory watched=s.memory watched))
  runAttemptEntryTransactionChecksCost (runAttemptAt 17) := by
 rcases tableOrigin with zero | tableAbove
 · have costEight : 8≤runAttemptEntryTransactionChecksCost := by
    calc
     8≤2^64-1 := by decide
     _≤(stateInitSourceCeiling+1)+(2^64-1) := Nat.le_add_left _ _
     _≤runAttemptEntryTransactionChecksCost := Nat.le_add_left _ _
   have aborted:=run_attempt_zero_header_entry_terminal_linked s si payload array count 2713731432 inputLength heap code atSi
    (fullDomain _ (by simp only [BitVec.add_zero];omega)) siCell linked zero heapGlobal
    (heapUpper.trans (by decide)) (costEight.trans budget)
   exact Or.inr (stAbort_mono s _ 8 runAttemptEntryTransactionChecksCost costEight aborted)
 · exact run_attempt_entry_transaction_checks_memory_reaches s si payload array count inputLength heap keccakState keccakPad
    stateArray stateCount codeArray codeCount output oldWs emptyRoot atSi siCell inputSmall inputBefore tableAbove linked stateLinked
    stateArrayAbove codeLinked codeArrayAbove scratchGlobal frameGlobal stateGlobal padGlobal outputGlobal wsGlobal emptyGlobal
    stateBelow padBelow outputBelow outputAligned fullDomain heapGlobal heapUpper code recordAbove recordBefore budget
#print axioms run_attempt_entry_transaction_checks_memory_all_headers
end InitECandidate.Runtime

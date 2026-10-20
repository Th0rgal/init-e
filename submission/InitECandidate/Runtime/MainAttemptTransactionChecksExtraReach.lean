import InitECandidate.Runtime.MainAttemptTransactionChecksFloorMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- The actual initializer and transaction-presence prefix retain the decoded
 extra-data length at pl+24. The cell comes from the original decoder, and all
 writes through state initialization are already framed by the actual prefix. -/
theorem main_attempt_transaction_checks_extra_reaches {F : Type}
 (s : PanSemStateFiniteExact 64 F) (initialGlobals : HolFiniteMapExact MlS (ValueHOL 64)) (depth : Nat)
 (si payload headers headerCount stateArray stateCount codeArray codeCount inputLength heap oldWs : BitVec 64)
 (code : s.code=originalRuntimeCode)
 (stateLinked : WitnessArrayLinked s si 40 48 stateArray stateCount 2713731432 inputLength heap)
 (codeLinked : WitnessArrayLinked s si 56 64 codeArray codeCount 2713731432 inputLength heap)
 (headerLinked : WitnessArrayLinked s si 72 80 headers headerCount 2713731432 inputLength heap)
 (payloadCell : s.memory (si+0#64)=.word payload)
 (inputSmall : inputLength.toNat≤134217712)
 (recordAfterInput : 2713731432+inputLength.toNat≤si.toNat)
 (recordBeforeHeap : si.toNat+88≤heap.toNat)
 (stateOrigin : stateCount=0 ∨si.toNat+88≤stateArray.toNat)
 (codeOrigin : codeCount=0 ∨si.toNat+88≤codeArray.toNat)
 (headerOrigin : headerCount=0 ∨si.toNat+88≤headers.toNat)
 (heapSmall : heap.toNat≤5000000040)
 (heapGlobal : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (initialized : ∀key,key≠ofString "heap_ptr"→s.globals.lookup key=(allInitializerGlobals initialGlobals).lookup key)
 (atOriginalWs : initialGlobals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (extraLength : BitVec 64)
 (extraCell : s.memory (payload+24#64)=.word extraLength)
 (extraBound : extraLength.toNat≤134217712)
 (payloadLower : 2713731432≤payload.toNat) (payloadExtent : payload.toNat+136≤heap.toNat)
 (budget : runAttemptEntryTransactionChecksCost≤s.clock-depth) :
 Reaches (attemptEntry s si depth) (runAttemptAt 0)
  (fun post=>StateInitHeapFloorReady heap.toNat post ∧post.code=originalRuntimeCode ∧post.memaddrs=s.memaddrs ∧
   post.locals.lookup (ofString "si")=some (.val (.word si)) ∧
   post.locals.lookup (ofString "pl")=some (.val (.word payload)) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<heap.toNat→post.memory watched=s.memory watched) ∧
   post.memaddrs (payload+24#64) ∧post.memory (payload+24#64)=.word extraLength ∧extraLength.toNat≤134217712)
  runAttemptEntryTransactionChecksCost (runAttemptAt 17) := by
 have prefixRun:=main_attempt_transaction_checks_floor_memory_reaches s initialGlobals depth si payload headers headerCount
  stateArray stateCount codeArray codeCount inputLength heap oldWs code stateLinked codeLinked headerLinked payloadCell
  inputSmall recordAfterInput recordBeforeHeap stateOrigin codeOrigin headerOrigin heapSmall heapGlobal initialized
  atOriginalWs fullDomain budget
 apply reaches_mono (attemptEntry s si depth) (runAttemptAt 0) (runAttemptAt 17) _ _ _ _ (le_refl _) ?_ prefixRun
 intro post facts
 obtain ⟨ready,installed,domain,atSi,atPayload,memory⟩:=facts
 have addressNat : (payload+24#64).toNat=payload.toNat+24 := by
  rw [BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  change payload.toNat+24<2^64
  omega
 refine ⟨ready,installed,domain,atSi,atPayload,memory,?_,?_,extraBound⟩
 · rw [domain]
   exact fullDomain _ (by rw [addressNat];omega)
 · rw [memory _ (by rw [addressNat];omega) (by rw [addressNat];omega)]
   exact extraCell
#print axioms main_attempt_transaction_checks_extra_reaches
end InitECandidate.Runtime

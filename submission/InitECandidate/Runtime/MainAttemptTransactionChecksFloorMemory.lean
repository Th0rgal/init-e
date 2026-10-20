import InitECandidate.Runtime.RunAttemptEntryTransactionChecksFloorMemoryAllHeaders
import InitECandidate.Runtime.AttemptWrapperGenericBound
import InitECandidate.Runtime.AllInitializerWorldGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Consume the actual main decoder's three witness links, allocation origins and
startup globals at the real attempt-entry context. No initializer-entry layout,
callee bound or execution frame is assumed. Depth nine is the main call site. -/
theorem main_attempt_transaction_checks_floor_memory_reaches {F : Type}
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
 (budget : runAttemptEntryTransactionChecksCost≤s.clock-depth) :
 Reaches (attemptEntry s si depth) (runAttemptAt 0)
  (fun post=>StateInitHeapFloorReady heap.toNat post ∧post.code=originalRuntimeCode ∧post.memaddrs=s.memaddrs ∧
   post.locals.lookup (ofString "si")=some (.val (.word si)) ∧
   post.locals.lookup (ofString "pl")=some (.val (.word payload)) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<heap.toNat→post.memory watched=s.memory watched))
  runAttemptEntryTransactionChecksCost (runAttemptAt 17) := by
 have globalWord (key : MlS) (notHeap : key≠ofString "heap_ptr") (pointer : BitVec 64)
  (actual : (allInitializerGlobals initialGlobals).lookup key=some (.val (.word pointer))) :
  (attemptEntry s si depth).globals.lookup key=some (.val (.word pointer)) :=
  (initialized key notHeap).trans actual
 have stateAbove : stateCount.toNat=0 ∨2713731432≤stateArray.toNat := by
  rcases stateOrigin with zero|above
  · left;rw [zero];rfl
  · right;omega
 have codeAbove : codeCount.toNat=0 ∨2713731432≤codeArray.toNat := by
  rcases codeOrigin with zero|above
  · left;rw [zero];rfl
  · right;omega
 have headersAbove : headerCount=0 ∨2713731432≤headers.toNat := by
  rcases headerOrigin with zero|above
  · exact Or.inl zero
  · right;omega
 exact run_attempt_entry_transaction_checks_floor_memory_all_headers (attemptEntry s si depth)
  si payload headers headerCount inputLength heap 2713714976 2713715176 stateArray stateCount codeArray codeCount
  2713717584 oldWs 2713717456 (attemptEntry_si s si depth) payloadCell inputSmall (by omega) headersAbove
  (headerLinked.after_frame s (attemptEntry s si depth) si 72 80 headers headerCount 2713731432 inputLength heap rfl rfl)
  (stateLinked.after_frame s (attemptEntry s si depth) si 40 48 stateArray stateCount 2713731432 inputLength heap rfl rfl)
  stateAbove
  (codeLinked.after_frame s (attemptEntry s si depth) si 56 64 codeArray codeCount 2713731432 inputLength heap rfl rfl)
  codeAbove
  (globalWord _ (by decide) _ (allInitializerGlobals_scratch initialGlobals))
  (globalWord _ (by decide) _ (allInitializerGlobals_frame initialGlobals))
  (globalWord _ (by decide) _ (allInitializerGlobals_keccak_state initialGlobals))
  (globalWord _ (by decide) _ (allInitializerGlobals_keccak_pad initialGlobals))
  (globalWord _ (by decide) _ (allInitializerGlobals_mpt_hash_scratch initialGlobals))
  (globalWord _ (by decide) _ ((allInitializerGlobals_world_kept initialGlobals).1.trans atOriginalWs))
  (globalWord _ (by decide) _ (allInitializerGlobals_empty_root initialGlobals))
  (by decide) (by decide) (by decide) (by decide) fullDomain heapGlobal (heapSmall.trans (by decide)) code
  (by omega) recordBeforeHeap budget
#print axioms main_attempt_transaction_checks_floor_memory_reaches
end InitECandidate.Runtime

import InitECandidate.Runtime.SystemMessageFieldsReach
import InitECandidate.Runtime.SystemMessageInterpreterInputs
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- The actual system transaction reaches process_message_call from its real
message allocation in at most 140 source clocks, carrying its source-assigned
30M gas word. All allocation/zeroing errors reject in that budget; the caller
supplies typed existing operands and the actual heap floor, not a gas bound. -/
theorem system_message_construction_entry_inputs_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer blockEnv txEnv systemAddress target data dataSize code codeSize : BitVec 64)
 (atBE : s.globals.lookup (ofString "be")=some (.val (.word blockEnv)))
 (atTE : s.locals.lookup (ofString "te")=some (.val (.word txEnv)))
 (atSystem : s.globals.lookup (ofString "vm_system_address")=some (.val (.word systemAddress)))
 (atTarget : s.locals.lookup (ofString "target")=some (.val (.word target)))
 (atData : s.locals.lookup (ofString "data")=some (.val (.word data)))
 (atSize : s.locals.lookup (ofString "data_n")=some (.val (.word dataSize)))
 (atCode : s.locals.lookup (ofString "code")=some (.rStruct [.val (.word code),.val (.word codeSize)]))
 (original : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (positive : 0<pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a) (budget : 140≤s.clock) :
 Reaches s (systemTransactionAt 8) (fun next=>SystemAccessInputContext s next pointer target data dataSize code codeSize) 140 (systemTransactionAt 26) := by
 have allocated:=msg_new_declaration_reaches s pointer (systemTransactionAt 9) original atHeap positive aligned capped (by omega)
 rw [←source_system_message_new] at allocated
 refine reaches_trans_budget s (systemTransactionAt 8) (systemTransactionAt 9) (systemTransactionAt 26)
  (MsgNewReady s pointer) (fun next=>SystemAccessInputContext s next pointer target data dataSize code codeSize) 42 98 budget allocated ?_
 intro mid facts remaining
 have fields:=system_message_fields_reaches s mid pointer blockEnv txEnv systemAddress target facts atBE atTE atSystem atTarget domain
 refine reaches_trans_budget mid (systemTransactionAt 9) (systemTransactionAt 14) (systemTransactionAt 26)
  (MsgNewReady s pointer) (fun next=>SystemAccessInputContext s next pointer target data dataSize code codeSize) 0 98 remaining fields ?_
 intro state ready ticks
 have targetAt : state.locals.lookup (ofString "target")=some (.val (.word target)):=
  (ready.locals _ (by decide)).trans atTarget
 have dataAt : state.locals.lookup (ofString "data")=some (.val (.word data)):=
  (ready.locals _ (by decide)).trans atData
 have sizeAt : state.locals.lookup (ofString "data_n")=some (.val (.word dataSize)):=
  (ready.locals _ (by decide)).trans atSize
 have codeAt : state.locals.lookup (ofString "code")=some (.rStruct [.val (.word code),.val (.word codeSize)]):=
  (ready.locals _ (by decide)).trans atCode
 have heapAt : state.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd pointer 176))) := by
  simp [ready.globals,HolFiniteMapExact.lookup_update,FUPDATE]
 have fullDomain : ∀a : BitVec 64,a.toNat<33806089496→state.memaddrs a := by
  intro a inside;rw [ready.domain];exact domain a inside
 have entry:=system_message_interpreter_entry_inputs_reaches state pointer target data dataSize code codeSize
  (allocationEnd pointer 176) ready.atMessage targetAt dataAt sizeAt codeAt (ready.code.trans original)
  heapAt ready.extent ready.aligned ready.capped fullDomain ticks
 have globalFrame : HeapGlobalsFrame s state := by
  intro key different
  rw [ready.globals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 refine reaches_mono state (systemTransactionAt 14) (systemTransactionAt 26)
  (fun post=>SystemAccessInputContext state post pointer target data dataSize code codeSize) (fun post=>SystemAccessInputContext s post pointer target data dataSize code codeSize)
  98 98 (Nat.le_refl 98) ?_ entry
 intro post result
 exact ⟨⟨result.atMessage,result.code,result.domain.trans ready.domain,result.gas,
  globalFrame.trans result.globals,result.heap⟩,result.inputs⟩
#print axioms system_message_construction_entry_inputs_reaches
end InitECandidate.Runtime

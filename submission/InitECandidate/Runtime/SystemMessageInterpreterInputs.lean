import InitECandidate.Runtime.SystemAccessInputsReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- From the real literal gas store through both actual accessed-set tables,
the system transaction reaches its original interpreter call with exactly
30M regular funding, or rejects within 98 source clocks. Message geometry is
concrete; no pre-existing gas bound, allocation reserve, or callee oracle is assumed. -/
theorem system_message_interpreter_entry_inputs_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (message target data dataSize code codeSize pointer : BitVec 64)
 (atMessage : s.locals.lookup (ofString "m")=some (.val (.word message)))
 (atTarget : s.locals.lookup (ofString "target")=some (.val (.word target)))
 (atData : s.locals.lookup (ofString "data")=some (.val (.word data)))
 (atSize : s.locals.lookup (ofString "data_n")=some (.val (.word dataSize)))
 (atCode : s.locals.lookup (ofString "code")=some (.rStruct [.val (.word code),.val (.word codeSize)]))
 (original : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (lower : message.toNat+176≤pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a) (budget : 98≤s.clock) :
 Reaches s (systemTransactionAt 14) (fun next=>SystemAccessInputContext s next message target data dataSize code codeSize) 98 (systemTransactionAt 26) := by
 have initialized:=system_message_gas_setup_exact_reaches s message target data dataSize code codeSize
  atMessage atTarget atData atSize atCode
 refine reaches_trans_budget s (systemTransactionAt 14) (systemTransactionAt 21) (systemTransactionAt 26)
  (fun post=>post=systemMessageGasSetupPost s message target data dataSize code codeSize)
  (fun next=>SystemAccessInputContext s next message target data dataSize code codeSize) 0 98 budget initialized ?_
 intro next facts remaining
 subst next
 let next:=systemMessageGasSetupPost s message target data dataSize code codeSize
 have inputs:=system_message_setup_post_inputs s message target data dataSize code codeSize
 have ctx : SystemAccessInputContext s next message target data dataSize code codeSize := by
  refine ⟨⟨atMessage,original,rfl,inputs.gas,?_,pointer,atHeap,lower,aligned,capped⟩,inputs⟩
  intro key different
  rfl
 exact system_access_tables_inputs_reaches s next message ctx domain remaining
#print axioms system_message_interpreter_entry_inputs_reaches
end InitECandidate.Runtime

import InitECandidate.Runtime.TeNewDeclarationReach
import InitECandidate.Runtime.SystemEnvironmentSetupReach
import InitECandidate.Runtime.SystemMessageConstructionEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- Actual system transaction from te_new through the interpreter entry,
including all setup stores and both accessed tables, in 206 clocks or rejection.
The 30M gas value is assigned by the source; no allocation reserve is assumed. -/
theorem system_environment_construction_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer blockEnv systemAddress target data dataSize code codeSize : BitVec 64)
 (atBE : s.globals.lookup (ofString "be")=some (.val (.word blockEnv)))
 (atSystem : s.globals.lookup (ofString "vm_system_address")=some (.val (.word systemAddress)))
 (atTarget : s.locals.lookup (ofString "target")=some (.val (.word target)))
 (atData : s.locals.lookup (ofString "data")=some (.val (.word data)))
 (atSize : s.locals.lookup (ofString "data_n")=some (.val (.word dataSize)))
 (atCode : s.locals.lookup (ofString "code")=some (.rStruct [.val (.word code),.val (.word codeSize)]))
 (original : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (positive : 0<pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a) (budget : 206≤s.clock) :
 Reaches s (systemTransactionAt 2) (fun next=>SystemAccessGasContext s next (allocationEnd pointer 200))
 206 (systemTransactionAt 26) := by
 have allocated:=te_new_declaration_reaches s pointer (systemTransactionAt 3) original atHeap positive aligned capped (by omega)
 rw [←source_system_environment_new] at allocated
 refine reaches_trans_budget s (systemTransactionAt 2) (systemTransactionAt 3) (systemTransactionAt 26)
  (TeNewReady s pointer) _ 66 140 budget allocated ?_
 intro mid ready remaining
 have setup:=system_environment_setup_reaches mid
 refine reaches_trans_budget mid (systemTransactionAt 3) (systemTransactionAt 8) (systemTransactionAt 26)
  (fun next=>next.locals=mid.locals ∧next.globals=mid.globals ∧next.code=mid.code ∧next.memaddrs=mid.memaddrs)
  _ 0 140 remaining setup ?_
 intro state kept ticks
 have localFrame : ∀key,key≠ofString "te"→state.locals.lookup key=s.locals.lookup key := by
  intro key different;rw [kept.1];exact ready.locals key different
 have globalFrame : HeapGlobalsFrame s state := by
  intro key different
  rw [kept.2.1,ready.globals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 have heapAt : state.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd pointer 200))) := by
  rw [kept.2.1,ready.globals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have teAt : state.locals.lookup (ofString "te")=some (.val (.word pointer)) := by
  rw [kept.1];exact ready.atEnvironment
 have fullDomain : ∀a : BitVec 64,a.toNat<33806089496→state.memaddrs a := by
  intro a inside;rw [kept.2.2.2,ready.domain];exact domain a inside
 have entry:=system_message_construction_entry_gas_reaches state (allocationEnd pointer 200)
  blockEnv pointer systemAddress target data dataSize code codeSize
  ((globalFrame _ (by decide)).trans atBE) teAt ((globalFrame _ (by decide)).trans atSystem)
  ((localFrame _ (by decide)).trans atTarget) ((localFrame _ (by decide)).trans atData)
  ((localFrame _ (by decide)).trans atSize) ((localFrame _ (by decide)).trans atCode)
  (kept.2.2.1.trans (ready.code.trans original)) heapAt (by have := ready.extent;omega)
  ready.aligned ready.capped fullDomain ticks
 refine reaches_mono state (systemTransactionAt 8) (systemTransactionAt 26) _ _ 140 140 (le_refl _) ?_ entry
 intro post result
 exact ⟨result.atMessage,result.code,result.domain.trans (kept.2.2.2.trans ready.domain),result.gas,
  globalFrame.trans result.globals,result.heap⟩
#print axioms system_environment_construction_entry_reaches
end InitECandidate.Runtime

import InitECandidate.Runtime.SystemAccessInputContext
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
variable {target data dataSize codePointer codeSize : BitVec 64}
private theorem source21 : systemTransactionAt 21=.decCall (ofString "aa") .one (ofString "htab_new") [.const 20,.const 8] (systemTransactionAt 22) := rfl
private theorem source22 : systemTransactionAt 22=.seq (.store (.op .add [.var .local (ofString "m"),.const 152]) (.var .local (ofString "aa"))) (systemTransactionAt 23) := rfl
private theorem source23 : systemTransactionAt 23=.decCall (ofString "ak") .one (ofString "htab_new") [.const 52,.const 8] (systemTransactionAt 24) := rfl
private theorem source24 : systemTransactionAt 24=.seq (.store (.op .add [.var .local (ofString "m"),.const 160]) (.var .local (ofString "ak"))) (systemTransactionAt 25) := rfl
private theorem source25 : systemTransactionAt 25=.seq .skip (systemTransactionAt 26) := rfl

private theorem after_key_table {F : Type} (base mid : PanSemStateFiniteExact 64 F) (message pointer : BitVec 64)
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (atPointer : mid.locals.lookup (ofString "ak")=some (.val (.word pointer)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) :
 Reaches mid (systemTransactionAt 24) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 0 (systemTransactionAt 26) := by
 have stored:=system_access_input_pointer_store_reaches base mid message pointer 160 (ofString "ak") (systemTransactionAt 25)
  ctx atPointer (by decide) (by decide) (by simp) domain
 rw [←source24] at stored
 exact reaches_trans mid (systemTransactionAt 24) (systemTransactionAt 25) (systemTransactionAt 26)
  (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 0 0 stored (by
   intro next facts
   rw [source25]
   exact reaches_seq next .skip (systemTransactionAt 26) 0 (fun post=>SystemAccessInputContext base post message target data dataSize codePointer codeSize)
    (Or.inl ⟨next,facts,by omega,by omega,evaluateHOLFiniteState_skip next⟩))

private theorem key_table {F : Type} (base mid : PanSemStateFiniteExact 64 F) (message : BitVec 64)
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) (budget : 49≤mid.clock) :
 Reaches mid (systemTransactionAt 23) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 49 (systemTransactionAt 26) := by
 obtain ⟨pointer,atHeap,lower,aligned,capped⟩:=ctx.heap
 have arena : ∀a : BitVec 64,a.toNat%8=0→pointer.toNat≤a.toNat→a.toNat<33806089496→mid.memaddrs a := by
  intro a _ _ inside;rw [ctx.domain];exact domain a inside
 have allocated:=access_table_declaration_reaches mid (ofString "ak") 52 pointer (systemTransactionAt 24)
  ctx.code atHeap aligned capped arena (by decide) budget
 rw [←source23] at allocated
 exact reaches_trans mid (systemTransactionAt 23) (systemTransactionAt 24) (systemTransactionAt 26)
  (AccessTableReady mid (ofString "ak") pointer 52) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 49 0 allocated (by
   intro next facts
   exact after_key_table base next message pointer
    (ctx.after_table atHeap lower aligned capped (by decide) facts) facts.1 domain)

private theorem after_address_table {F : Type} (base mid : PanSemStateFiniteExact 64 F) (message pointer : BitVec 64)
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (atPointer : mid.locals.lookup (ofString "aa")=some (.val (.word pointer)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) (budget : 49≤mid.clock) :
 Reaches mid (systemTransactionAt 22) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 49 (systemTransactionAt 26) := by
 have stored:=system_access_input_pointer_store_reaches base mid message pointer 152 (ofString "aa") (systemTransactionAt 23)
  ctx atPointer (by decide) (by decide) (by simp) domain
 rw [←source22] at stored
 exact reaches_trans_budget mid (systemTransactionAt 22) (systemTransactionAt 23) (systemTransactionAt 26)
  (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 0 49 budget stored
  (fun next facts remaining=>key_table base next message facts domain remaining)

/-- Both actual accessed-set constructors and pointer stores preserve the
30M regular-gas word at the actual process_message_call entry. Every failed
allocation aborts within the same fixed source budget; no reserve is assumed. -/
theorem system_access_tables_inputs_reaches {F : Type} (base mid : PanSemStateFiniteExact 64 F) (message : BitVec 64)
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) (budget : 98≤mid.clock) :
 Reaches mid (systemTransactionAt 21) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 98 (systemTransactionAt 26) := by
 obtain ⟨pointer,atHeap,lower,aligned,capped⟩:=ctx.heap
 have arena : ∀a : BitVec 64,a.toNat%8=0→pointer.toNat≤a.toNat→a.toNat<33806089496→mid.memaddrs a := by
  intro a _ _ inside;rw [ctx.domain];exact domain a inside
 have allocated:=access_table_declaration_reaches mid (ofString "aa") 20 pointer (systemTransactionAt 22)
  ctx.code atHeap aligned capped arena (by decide) (by omega)
 rw [←source21] at allocated
 exact reaches_trans_budget mid (systemTransactionAt 21) (systemTransactionAt 22) (systemTransactionAt 26)
  (AccessTableReady mid (ofString "aa") pointer 20) (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 49 49 budget allocated (by
   intro next facts remaining
   exact after_address_table base next message pointer
    (ctx.after_table atHeap lower aligned capped (by decide) facts) facts.1 domain remaining)
#print axioms system_access_tables_inputs_reaches
end InitECandidate.Runtime

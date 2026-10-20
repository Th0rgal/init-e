import InitECandidate.Runtime.MsgNewReadyStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem source9 : systemTransactionAt 9=.seq (.store (.op .add [.var .local (ofString "m"),.const 0]) (.var .global (ofString "be"))) (systemTransactionAt 10) := rfl
private theorem source10 : systemTransactionAt 10=.seq (.store (.op .add [.var .local (ofString "m"),.const 8]) (.var .local (ofString "te"))) (systemTransactionAt 11) := rfl
private theorem source11 : systemTransactionAt 11=.seq (.store (.op .add [.var .local (ofString "m"),.const 16]) (.var .global (ofString "vm_system_address"))) (systemTransactionAt 12) := rfl
private theorem source12 : systemTransactionAt 12=.seq (.store (.op .add [.var .local (ofString "m"),.const 24]) (.var .local (ofString "target"))) (systemTransactionAt 13) := rfl
private theorem source13 : systemTransactionAt 13=.seq (.store (.op .add [.var .local (ofString "m"),.const 32]) (.var .local (ofString "target"))) (systemTransactionAt 14) := rfl

/-- The five actual pre-gas stores preserve the message constructor's extent,
heap and old-memory frame. All typed operands come from concrete caller locals
and globals, and the actual arena domain supplies their destination cells. -/
theorem system_message_fields_reaches {F : Type} (base mid : PanSemStateFiniteExact 64 F)
 (pointer blockEnv txEnv systemAddress target : BitVec 64)
 (ctx : MsgNewReady base pointer mid)
 (atBE : base.globals.lookup (ofString "be")=some (.val (.word blockEnv)))
 (atTE : base.locals.lookup (ofString "te")=some (.val (.word txEnv)))
 (atSystem : base.globals.lookup (ofString "vm_system_address")=some (.val (.word systemAddress)))
 (atTarget : base.locals.lookup (ofString "target")=some (.val (.word target)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) :
 Reaches mid (systemTransactionAt 9) (MsgNewReady base pointer) 0 (systemTransactionAt 14) := by
 have stage13 (state : PanSemStateFiniteExact 64 F) (facts : MsgNewReady base pointer state) :
  Reaches state (systemTransactionAt 13) (MsgNewReady base pointer) 0 (systemTransactionAt 14) := by
  rw [source13]
  apply msg_new_ready_store_reaches base state pointer 32 target _ (systemTransactionAt 14) facts (by decide) domain
  have value : state.locals.lookup (ofString "target")=some (.val (.word target)) :=
   (facts.locals _ (by decide)).trans atTarget
  simp [evalHOLExact,value]
 have stage12 (state : PanSemStateFiniteExact 64 F) (facts : MsgNewReady base pointer state) :
  Reaches state (systemTransactionAt 12) (MsgNewReady base pointer) 0 (systemTransactionAt 13) := by
  rw [source12]
  apply msg_new_ready_store_reaches base state pointer 24 target _ (systemTransactionAt 13) facts (by decide) domain
  have value : state.locals.lookup (ofString "target")=some (.val (.word target)) :=
   (facts.locals _ (by decide)).trans atTarget
  simp [evalHOLExact,value]
 have stage11 (state : PanSemStateFiniteExact 64 F) (facts : MsgNewReady base pointer state) :
  Reaches state (systemTransactionAt 11) (MsgNewReady base pointer) 0 (systemTransactionAt 12) := by
  rw [source11]
  apply msg_new_ready_store_reaches base state pointer 16 systemAddress _ (systemTransactionAt 12) facts (by decide) domain
  have value : state.globals.lookup (ofString "vm_system_address")=some (.val (.word systemAddress)) := by
   simpa (config:={decide:=true}) [facts.globals,HolFiniteMapExact.lookup_update,FUPDATE] using atSystem
  simp [evalHOLExact,value]
 have stage10 (state : PanSemStateFiniteExact 64 F) (facts : MsgNewReady base pointer state) :
  Reaches state (systemTransactionAt 10) (MsgNewReady base pointer) 0 (systemTransactionAt 11) := by
  rw [source10]
  apply msg_new_ready_store_reaches base state pointer 8 txEnv _ (systemTransactionAt 11) facts (by decide) domain
  have value : state.locals.lookup (ofString "te")=some (.val (.word txEnv)) :=
   (facts.locals _ (by decide)).trans atTE
  simp [evalHOLExact,value]
 have stage9 (state : PanSemStateFiniteExact 64 F) (facts : MsgNewReady base pointer state) :
  Reaches state (systemTransactionAt 9) (MsgNewReady base pointer) 0 (systemTransactionAt 10) := by
  rw [source9]
  apply msg_new_ready_store_reaches base state pointer 0 blockEnv _ (systemTransactionAt 10) facts (by decide) domain
  have value : state.globals.lookup (ofString "be")=some (.val (.word blockEnv)) := by
   simpa (config:={decide:=true}) [facts.globals,HolFiniteMapExact.lookup_update,FUPDATE] using atBE
  simp [evalHOLExact,value]
 refine reaches_trans mid (systemTransactionAt 9) (systemTransactionAt 10) (systemTransactionAt 14)
  (MsgNewReady base pointer) (MsgNewReady base pointer) 0 0 (stage9 mid ctx) ?_
 intro state facts
 refine reaches_trans state (systemTransactionAt 10) (systemTransactionAt 11) (systemTransactionAt 14)
  (MsgNewReady base pointer) (MsgNewReady base pointer) 0 0 (stage10 state facts) ?_
 intro state facts
 refine reaches_trans state (systemTransactionAt 11) (systemTransactionAt 12) (systemTransactionAt 14)
  (MsgNewReady base pointer) (MsgNewReady base pointer) 0 0 (stage11 state facts) ?_
 intro state facts
 refine reaches_trans state (systemTransactionAt 12) (systemTransactionAt 13) (systemTransactionAt 14)
  (MsgNewReady base pointer) (MsgNewReady base pointer) 0 0 (stage12 state facts) ?_
 intro state facts
 exact stage13 state facts
#print axioms system_message_fields_reaches
end InitECandidate.Runtime

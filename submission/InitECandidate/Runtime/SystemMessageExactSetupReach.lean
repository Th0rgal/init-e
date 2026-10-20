import InitECandidate.Runtime.SystemMessageGasSetup
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private theorem reaches_known_word_store {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination value : ExpHOL 64) (address word : BitVec 64) (tail : ProgHOL 64)
 (atAddress : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
 (atValue : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) value=some (.val (.word word))) :
 Reaches s (.seq (.store destination value) tail) (fun post=>post=sourceWriteWord s address word) 0 tail := by
 classical
 apply reaches_seq
 by_cases domain : s.memaddrs address
 · exact Or.inl ⟨_,rfl,by simp [sourceWriteWord],by simp [sourceWriteWord],
    evaluate_store_word s address word destination value atAddress atValue domain⟩
 · have failed : evaluateHOLFiniteState s (.store destination value)=(some .error,s) := by
    rw [evaluateHOLFiniteState_store,atAddress,atValue]
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,domain]
   right
   rw [failed]
   exact stAbort_error s 0

noncomputable def systemMessageGasSetupPost {F : Type} (s : PanSemStateFiniteExact 64 F)
 (message target data dataSize code codeSize : BitVec 64) : PanSemStateFiniteExact 64 F :=
 sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord
  (sourceWriteWord s (message+40) 30000000) (message+48) ((97920#64)*(16#64)))
  (message+88) data) (message+96) dataSize) (message+104) target) (message+112) code) (message+120) codeSize

/-- Seven real stores beginning at the literal 30M message-gas assignment.
All unmapped stores reject; no room or readable-memory premise is needed.
The endpoint is immediately before the two accessed-set constructors. -/
theorem system_message_gas_setup_exact_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (message target data dataSize code codeSize : BitVec 64)
 (atMessage : s.locals.lookup (ofString "m")=some (.val (.word message)))
 (atTarget : s.locals.lookup (ofString "target")=some (.val (.word target)))
 (atData : s.locals.lookup (ofString "data")=some (.val (.word data)))
 (atSize : s.locals.lookup (ofString "data_n")=some (.val (.word dataSize)))
 (atCode : s.locals.lookup (ofString "code")=some (.rStruct [.val (.word code),.val (.word codeSize)])) :
 Reaches s (systemTransactionAt 14)
  (fun post=>post=systemMessageGasSetupPost s message target data dataSize code codeSize) 0 (systemTransactionAt 21) := by
 let s1:=sourceWriteWord s (message+40) 30000000
 let s2:=sourceWriteWord s1 (message+48) ((97920#64)*(16#64))
 let s3:=sourceWriteWord s2 (message+88) data
 let s4:=sourceWriteWord s3 (message+96) dataSize
 let s5:=sourceWriteWord s4 (message+104) target
 let s6:=sourceWriteWord s5 (message+112) code
 let s7:=sourceWriteWord s6 (message+120) codeSize
 have r0 : Reaches s (systemTransactionAt 14) (fun post=>post=s1) 0 (systemTransactionAt 15) := by
  change Reaches s (.seq (.store (.op .add [.var .local (ofString "m"),.const 40]) (.const 30000000)) (systemTransactionAt 15)) _ _ _
  apply reaches_known_word_store s _ _ (message+40) 30000000 (systemTransactionAt 15)
  · simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r1 : Reaches s1 (systemTransactionAt 15) (fun post=>post=s2) 0 (systemTransactionAt 16) := by
  change Reaches s1 (.seq (.store (.op .add [.var .local (ofString "m"),.const 48]) (.panop .mul [.const 97920,.const 16])) (systemTransactionAt 16)) _ _ _
  apply reaches_known_word_store s1 _ _ (message+48) ((97920#64)*(16#64)) (systemTransactionAt 16)
  · simp [s1,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r2 : Reaches s2 (systemTransactionAt 16) (fun post=>post=s3) 0 (systemTransactionAt 17) := by
  change Reaches s2 (.seq (.store (.op .add [.var .local (ofString "m"),.const 88]) (.var .local (ofString "data"))) (systemTransactionAt 17)) _ _ _
  apply reaches_known_word_store s2 _ _ (message+88) data (systemTransactionAt 17)
  · simp [s1,s2,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,s2,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r3 : Reaches s3 (systemTransactionAt 17) (fun post=>post=s4) 0 (systemTransactionAt 18) := by
  change Reaches s3 (.seq (.store (.op .add [.var .local (ofString "m"),.const 96]) (.var .local (ofString "data_n"))) (systemTransactionAt 18)) _ _ _
  apply reaches_known_word_store s3 _ _ (message+96) dataSize (systemTransactionAt 18)
  · simp [s1,s2,s3,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,s2,s3,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r4 : Reaches s4 (systemTransactionAt 18) (fun post=>post=s5) 0 (systemTransactionAt 19) := by
  change Reaches s4 (.seq (.store (.op .add [.var .local (ofString "m"),.const 104]) (.var .local (ofString "target"))) (systemTransactionAt 19)) _ _ _
  apply reaches_known_word_store s4 _ _ (message+104) target (systemTransactionAt 19)
  · simp [s1,s2,s3,s4,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,s2,s3,s4,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r5 : Reaches s5 (systemTransactionAt 19) (fun post=>post=s6) 0 (systemTransactionAt 20) := by
  change Reaches s5 (.seq (.store (.op .add [.var .local (ofString "m"),.const 112]) (.rfield 0 (.var .local (ofString "code")))) (systemTransactionAt 20)) _ _ _
  apply reaches_known_word_store s5 _ _ (message+112) code (systemTransactionAt 20)
  · simp [s1,s2,s3,s4,s5,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,s2,s3,s4,s5,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have r6 : Reaches s6 (systemTransactionAt 20) (fun post=>post=s7) 0 (systemTransactionAt 21) := by
  change Reaches s6 (.seq (.store (.op .add [.var .local (ofString "m"),.const 120]) (.rfield 1 (.var .local (ofString "code")))) (systemTransactionAt 21)) _ _ _
  apply reaches_known_word_store s6 _ _ (message+120) codeSize (systemTransactionAt 21)
  · simp [s1,s2,s3,s4,s5,s6,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  · simp [s1,s2,s3,s4,s5,s6,sourceWriteWord,evalHOLExact,evalListHOLExact,atMessage,atTarget,atData,atSize,atCode,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
 have all : Reaches s (systemTransactionAt 14) (fun post=>post=s7) 0 (systemTransactionAt 21) := by
  refine reaches_trans s (systemTransactionAt 14) (systemTransactionAt 15) (systemTransactionAt 21) (fun post=>post=s1) (fun post=>post=s7) 0 0 r0 ?_
  intro next equal;subst next
  refine reaches_trans s1 (systemTransactionAt 15) (systemTransactionAt 16) (systemTransactionAt 21) (fun post=>post=s2) (fun post=>post=s7) 0 0 r1 ?_
  intro next equal;subst next
  refine reaches_trans s2 (systemTransactionAt 16) (systemTransactionAt 17) (systemTransactionAt 21) (fun post=>post=s3) (fun post=>post=s7) 0 0 r2 ?_
  intro next equal;subst next
  refine reaches_trans s3 (systemTransactionAt 17) (systemTransactionAt 18) (systemTransactionAt 21) (fun post=>post=s4) (fun post=>post=s7) 0 0 r3 ?_
  intro next equal;subst next
  refine reaches_trans s4 (systemTransactionAt 18) (systemTransactionAt 19) (systemTransactionAt 21) (fun post=>post=s5) (fun post=>post=s7) 0 0 r4 ?_
  intro next equal;subst next
  refine reaches_trans s5 (systemTransactionAt 19) (systemTransactionAt 20) (systemTransactionAt 21) (fun post=>post=s6) (fun post=>post=s7) 0 0 r5 ?_
  intro next equal;subst next
  exact r6
 exact all
#print axioms system_message_gas_setup_exact_reaches
end InitECandidate.Runtime

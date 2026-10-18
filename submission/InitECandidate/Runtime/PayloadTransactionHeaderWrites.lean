import InitECandidate.Runtime.PayloadTransactionHeaderFrame
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def payloadTransactionHeaderPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count : BitVec 64) : PanSemStateFiniteExact 64 F :=
  sourceWriteWord (sourceWriteWord state (payload + 32) array) (payload + 40) count

/-- Successful original header stores install the transaction-array pointer
and count read later by versioned-hash validation. -/
theorem evaluate_payload_transaction_header_writes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atList : state.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]))
    (arrayDomain : state.memaddrs (payload + 32)) (countDomain : state.memaddrs (payload + 40)) :
    evaluateHOLFiniteState state payloadTransactionHeader = (none,payloadTransactionHeaderPost state payload array count) := by
  have one := evaluate_store_word state (payload + 32) array
    (.op .add [.var .local (ofString "pl"),.const 32]) (.rfield 0 (.var .local (ofString "txs")))
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atList]) arrayDomain
  have two := evaluate_store_word (sourceWriteWord state (payload + 32) array) (payload + 40) count
    (.op .add [.var .local (ofString "pl"),.const 40]) (.rfield 1 (.var .local (ofString "txs")))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atList]) countDomain
  exact evaluate_seq_none one two

theorem payload_transaction_header_readback {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count : BitVec 64) :
    (payloadTransactionHeaderPost state payload array count).memory (payload + 32) = .word array ∧
    (payloadTransactionHeaderPost state payload array count).memory (payload + 40) = .word count := by
  simp [payloadTransactionHeaderPost,sourceWriteWord]


#print axioms evaluate_payload_transaction_header_writes
#print axioms payload_transaction_header_readback
end InitECandidate.Runtime

import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadInputHeader : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "pl"),.const 0]) (.var .local (ofString "p")))
    (.store (.op .add [.var .local (ofString "pl"),.const 8]) (.var .local (ofString "len")))

noncomputable def payloadInputHeaderPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length : BitVec 64) : PanSemStateFiniteExact 64 F :=
  sourceWriteWord (sourceWriteWord state (payload + 0) pointer) (payload + 8) length

theorem source_payload_input_header : payloadAt 2 =
    .seq (.store (.op .add [.var .local (ofString "pl"),.const 0]) (.var .local (ofString "p")))
    (.seq (.store (.op .add [.var .local (ofString "pl"),.const 8]) (.var .local (ofString "len"))) (payloadAt 4)) := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_payload_input_header_writes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (pointerDomain : state.memaddrs (payload + 0)) (lengthDomain : state.memaddrs (payload + 8)) :
    evaluateHOLFiniteState state payloadInputHeader = (none,payloadInputHeaderPost state payload pointer length) := by
  have one := evaluate_store_word state (payload + 0) pointer
    (.op .add [.var .local (ofString "pl"),.const 0]) (.var .local (ofString "p"))
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atPointer]) pointerDomain
  have two := evaluate_store_word (sourceWriteWord state (payload + 0) pointer) (payload + 8) length
    (.op .add [.var .local (ofString "pl"),.const 8]) (.var .local (ofString "len"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atLength]) lengthDomain
  exact evaluate_seq_none one two

theorem payload_input_header_readback {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length : BitVec 64) :
    (payloadInputHeaderPost state payload pointer length).memory (payload + 0) = .word pointer ∧
    (payloadInputHeaderPost state payload pointer length).memory (payload + 8) = .word length := by
  simp [payloadInputHeaderPost,sourceWriteWord]

#print axioms evaluate_payload_input_header_writes
#print axioms payload_input_header_readback
end InitECandidate.Runtime

import InitECandidate.Runtime.HtrRequestsSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrNewPayloadAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_new_payload_request)

def htrNewPayloadRead (offset : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "si"),.const offset])

def htrNewPayloadAddress (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .local (ofString "ch"),.const offset]

def htrNewPayloadPayloadArguments : List (ExpHOL 64) := [htrNewPayloadRead 0,.var .local (ofString "ch")]
def htrNewPayloadBlobsArguments : List (ExpHOL 64) :=
  [htrNewPayloadRead 8,htrNewPayloadRead 16,htrNewPayloadRead 16,htrNewPayloadAddress 32]
def htrNewPayloadCopyArguments : List (ExpHOL 64) := [htrNewPayloadAddress 64,htrNewPayloadRead 24,.const 32]
def htrNewPayloadRequestsArguments : List (ExpHOL 64) := [htrNewPayloadRead 32,htrNewPayloadAddress 96]
def htrNewPayloadMerkleArguments : List (ExpHOL 64) :=
  [.var .local (ofString "ch"),.const 4,.const 4,.var .local (ofString "out")]

theorem source_htrNewPayload_mark : htrNewPayloadAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrNewPayloadAt 1) := by rfl

theorem source_htrNewPayload_alloc : htrNewPayloadAt 1 =
    .decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 4,.const 32]] (htrNewPayloadAt 2) := by rfl

theorem source_htrNewPayload_payload : htrNewPayloadAt 2 =
    .seq (.call (some (none,none)) (ofString "htr_payload") htrNewPayloadPayloadArguments) (htrNewPayloadAt 3) := by rfl

theorem source_htrNewPayload_blobs : htrNewPayloadAt 3 =
    .seq (.call (some (none,none)) (ofString "htr_plist_chunks") htrNewPayloadBlobsArguments) (htrNewPayloadAt 4) := by rfl

theorem source_htrNewPayload_copy : htrNewPayloadAt 4 =
    .seq (.call (some (none,none)) (ofString "memcpy") htrNewPayloadCopyArguments) (htrNewPayloadAt 5) := by rfl

theorem source_htrNewPayload_requests : htrNewPayloadAt 5 =
    .seq (.call (some (none,none)) (ofString "htr_requests") htrNewPayloadRequestsArguments) (htrNewPayloadAt 6) := by rfl

theorem source_htrNewPayload_merkle : htrNewPayloadAt 6 =
    .seq (.call (some (none,none)) (ofString "merkleize") htrNewPayloadMerkleArguments) (htrNewPayloadAt 7) := by rfl

theorem source_htrNewPayload_finish : htrNewPayloadAt 7 =
    .seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)) := by rfl

theorem htrNewPayload_requests_arguments {F : Type} (state : PanSemStateFiniteExact 64 F) (si chunks record : BitVec 64)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (domain : state.memaddrs (si + (32#64))) (cell : state.memory (si + (32#64)) = .word record) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadRequestsArguments =
      some [.val (.word record),.val (.word (chunks + (96#64)))] := by
  simp [htrNewPayloadRequestsArguments,htrNewPayloadRead,htrNewPayloadAddress,evalListHOLExact,evalHOLExact,
    atSi,atChunks,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,cell]

#print axioms source_htrNewPayload_payload
#print axioms source_htrNewPayload_requests
#print axioms source_htrNewPayload_merkle
#print axioms htrNewPayload_requests_arguments
end InitECandidate.Runtime

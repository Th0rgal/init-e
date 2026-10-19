import InitECandidate.Runtime.HtrRequestListDecodedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrRequestsAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_requests)

def htrRequestsListArguments (index size outputOffset : BitVec 64) : List (ExpHOL 64) :=
  [.const index,.load .one (.op .add [.var .local (ofString "rq"),.const (index * (16#64))]),
   .load .one (.op .add [.var .local (ofString "rq"),.const (index * (16#64) + (8#64))]),
   .const size,recordHashAddress (ofString "ch") outputOffset]

theorem htrRequests_list_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record index pointer count chunks size offset : BitVec 64)
    (atRecord : state.locals.lookup (ofString "rq") = some (.val (.word record)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (entry : RlpSliceEntry state record index pointer count) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (htrRequestsListArguments index size offset) =
      some [.val (.word index),.val (.word pointer),.val (.word count),.val (.word size),.val (.word (chunks + offset))] := by
  have lengthDomain : state.memaddrs (record + (index * (16#64) + (8#64))) := by
    simpa only [BitVec.add_assoc] using entry.lengthDomain
  have lengthCell : state.memory (record + (index * (16#64) + (8#64))) = .word count := by
    simpa only [BitVec.add_assoc] using entry.lengthCell
  simp [htrRequestsListArguments,evalListHOLFinite,evalListHOLExact,recordHashAddress_eval state _ chunks offset atChunks,
    evalHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    entry.pointerDomain,entry.pointerCell,lengthDomain,lengthCell]

theorem source_htrRequests_mark : htrRequestsAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrRequestsAt 1) := by rfl

theorem source_htrRequests_alloc : htrRequestsAt 1 =
    .decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 5,.const 32]] (htrRequestsAt 2) := by rfl

theorem source_htrRequests_list_0 : htrRequestsAt 2 =
    .seq (.call (some (none,none)) (ofString "htr_request_list") (htrRequestsListArguments 0 192 0)) (htrRequestsAt 3) := by rfl

theorem source_htrRequests_list_1 : htrRequestsAt 3 =
    .seq (.call (some (none,none)) (ofString "htr_request_list") (htrRequestsListArguments 1 76 32)) (htrRequestsAt 4) := by rfl

theorem source_htrRequests_list_2 : htrRequestsAt 4 =
    .seq (.call (some (none,none)) (ofString "htr_request_list") (htrRequestsListArguments 2 116 64)) (htrRequestsAt 5) := by rfl

theorem source_htrRequests_list_3 : htrRequestsAt 5 =
    .seq (.call (some (none,none)) (ofString "htr_request_list") (htrRequestsListArguments 3 184 96)) (htrRequestsAt 6) := by rfl

theorem source_htrRequests_list_4 : htrRequestsAt 6 =
    .seq (.call (some (none,none)) (ofString "htr_request_list") (htrRequestsListArguments 4 68 128)) (htrRequestsAt 7) := by rfl

theorem source_htrRequests_hash : htrRequestsAt 7 =
    .seq (.call (some (none,none)) (ofString "htr_pcontainer")
      [.var .local (ofString "ch"),.const 5,.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0))) := by rfl

#print axioms htrRequests_list_arguments
#print axioms source_htrRequests_mark
#print axioms source_htrRequests_alloc
#print axioms source_htrRequests_list_0
#print axioms source_htrRequests_list_1
#print axioms source_htrRequests_list_2
#print axioms source_htrRequests_list_3
#print axioms source_htrRequests_list_4
#print axioms source_htrRequests_hash
end InitECandidate.Runtime

import InitECandidate.Runtime.RlpEncodeBytesCallBound
import InitECandidate.Runtime.RlpLengthRuntimeBounds
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def rlpFinishListAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_rlp_finish_list)
def rlpFinishListHeaderArguments : List (ExpHOL 64) := [.var .local (ofString "dst"),.var .local (ofString "payload")]
def rlpFinishListCopyArguments : List (ExpHOL 64) :=
 [.op .add [.var .local (ofString "dst"),.var .local (ofString "hl")],
  .op .add [.var .local (ofString "dst"),.const (9#64)],.var .local (ofString "payload")]
def rlpFinishListCopyTail : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") rlpFinishListCopyArguments)
 (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") rlpFinishListHeaderArguments)
  (.return (.op .add [.var .local (ofString "hl"),.var .local (ofString "payload")])))
def rlpFinishListTailCost (length : Nat) : Nat := (length/32+length/8+11)+(rlpWriterSourceCost+2)
def rlpFinishListSourceCost (length : Nat) : Nat := ((2^64-1)+3)+rlpFinishListTailCost length

theorem rlp_finish_list_copy_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (dst length : BitVec 64) (header : ValueHOL 64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atLen : s.locals.lookup (ofString "payload")=some (.val (.word length)))
 (atHeader : s.locals.lookup (ofString "hl")=some header)
 (code : s.code=originalRuntimeCode) (small : length.toNat≤2^62)
 (budget : rlpFinishListTailCost length.toNat≤s.clock) :
 RunBounded s rlpFinishListCopyTail (rlpFinishListTailCost length.toNat) := by
 cases header with
 | val held=>
  cases held with
  | word h=>
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) rlpFinishListCopyArguments=
    some [.val (.word (dst+h)),.val (.word (dst+9#64)),.val (.word length)] := by
    simp [rlpFinishListCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atLen,atHeader,
     wordOpHOL,wordOp,valueIsWord,valueWord]
   have copied:=evaluate_memcpy_call_wide_bounded s rlpFinishListCopyArguments (dst+h) (dst+9#64) length args code small (by
    unfold rlpFinishListTailCost at budget;omega)
   have tail : ProgBounded (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") rlpFinishListHeaderArguments)
    (.return (.op .add [.var .local (ofString "hl"),.var .local (ofString "payload")]))) (rlpWriterSourceCost+2) := by
    intro G post installed ticks
    have b:=ProgBounded.seq (ProgBounded.call rlp_encode_list_header_fun_bounded none rlpFinishListHeaderArguments)
     (ProgBounded.straight (.return (.op .add [.var .local (ofString "hl"),.var .local (ofString "payload")])) rfl)
     post installed (by simpa [Nat.add_assoc] using ticks)
    simpa [Nat.add_assoc] using b
   exact RunBounded.seq copied budget (by intro post run installed ticks;exact tail post (installed.trans code) ticks)
 | rStruct fields=>
  simp [RunBounded,rlpFinishListCopyTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,
   rlpFinishListCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atLen,atHeader,wordOpHOL,valueIsWord]
 | nStruct name fields=>
  simp [RunBounded,rlpFinishListCopyTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,
   rlpFinishListCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atLen,atHeader,wordOpHOL,valueIsWord]

theorem rlp_finish_list_after_payload_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (dst length : BitVec 64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atLen : s.locals.lookup (ofString "payload")=some (.val (.word length)))
 (code : s.code=originalRuntimeCode) (small : length.toNat≤2^62)
 (budget : rlpFinishListSourceCost length.toNat≤s.clock) :
 RunBounded s (rlpFinishListAt 1) (rlpFinishListSourceCost length.toNat) := by
 change RunBounded s (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
  [.var .local (ofString "payload")] rlpFinishListCopyTail) _
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "payload")]=
  some [.val (.word length)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLen]
 apply RunBounded.decCall args budget
 intro body callee shape lookup
 have bounded:=ProgBounded.bodies_of_fun rlp_list_header_length_fun_bounded s code (by
  unfold rlpFinishListSourceCost at budget;omega) _ _ _ _ lookup
 refine ⟨bounded,?_⟩
 intro value post returned remaining
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
 rw [returned] at metadata
 apply rlp_finish_list_copy_tail_bounded _ dst length value
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atDst
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLen
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact metadata.1.trans code
 · exact small
 · exact remaining

/-- Actual list finisher: byte count is the real pointer difference; unreadable
 buffers and failed stores are included in the bound. -/
theorem rlp_finish_list_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (dst payloadEnd : BitVec 64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atEnd : s.locals.lookup (ofString "payload_end")=some (.val (.word payloadEnd)))
 (code : s.code=originalRuntimeCode) (small : (payloadEnd-(dst+9#64)).toNat≤2^62)
 (budget : rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_rlp_finish_list)
  (rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat) := by
 let length:=payloadEnd-(dst+9#64)
 let ready:=setVarHOLFinite (ofString "payload") (.val (.word length)) s
 have bounded:=rlp_finish_list_after_payload_bounded ready dst length
  (by simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atDst)
  (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) code small budget
 have evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .sub [.var .local (ofString "payload_end"),.op .add [.var .local (ofString "dst"),.const (9#64)]])=
  some (.val (.word length)) := by
  simp [evalHOLExact,evalListHOLExact,atDst,atEnd,wordOpHOL,wordOp,valueIsWord,valueWord,length]
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (.dec (ofString "payload") .one
  (.op .sub [.var .local (ofString "payload_end"),.op .add [.var .local (ofString "dst"),.const (9#64)]]) (rlpFinishListAt 1)) _
 unfold RunBounded at bounded ⊢
 rw [evaluateHOLFiniteState_dec_total]
 simp only [evaluated,shapeOfHOLExact,shapeEqHOL,if_true]
 exact bounded
#print axioms rlp_finish_list_body_bounded
end InitECandidate.Runtime

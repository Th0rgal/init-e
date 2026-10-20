import InitECandidate.Runtime.RlpWritersRuntimeBound
import InitECandidate.Runtime.EncWriters2GD
import InitECandidate.Runtime.MemcpyWideCallBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def rlpEncodeBytesGuard : ProgHOL 64 := match ebBody with | .seq first _=>first | _=>.skip
def rlpEncodeBytesCopyArguments : List (ExpHOL 64) :=
 [.op .add [.var .local (ofString "dst"),.var .local (ofString "h")],.var .local (ofString "src"),.var .local (ofString "n")]
def rlpEncodeBytesCopyTail : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") rlpEncodeBytesCopyArguments)
 (.return (.op .add [.var .local (ofString "h"),.var .local (ofString "n")]))
def rlpEncodeBytesSourceCost (length : Nat) : Nat := rlpWriterSourceCost+1+(length/32+length/8+11)

theorem rlp_encode_bytes_copy_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination source length : BitVec 64) (header : ValueHOL 64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word destination)))
 (atSrc : s.locals.lookup (ofString "src")=some (.val (.word source)))
 (atLen : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (atHeader : s.locals.lookup (ofString "h")=some header)
 (code : s.code=originalRuntimeCode) (small : length.toNat≤2^62)
 (budget : length.toNat/32+length.toNat/8+11≤s.clock) :
 RunBounded s rlpEncodeBytesCopyTail (length.toNat/32+length.toNat/8+11) := by
 cases header with
 | val held=>
  cases held with
  | word h=>
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) rlpEncodeBytesCopyArguments=
    some [.val (.word (destination+h)),.val (.word source),.val (.word length)] := by
    simp [rlpEncodeBytesCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atSrc,atLen,atHeader,
     wordOpHOL,wordOp,valueIsWord,valueWord]
   have copied:=evaluate_memcpy_call_wide_bounded s rlpEncodeBytesCopyArguments (destination+h) source length args code small budget
   have bounded:=RunBounded.seq (tail:=.return (.op .add [.var .local (ofString "h"),.var .local (ofString "n")])) copied (b:=0) (by simpa only [Nat.add_zero] using budget) (by
    intro post run installed ticks
    exact ProgBounded.straight _ rfl post (installed.trans code) ticks)
   simpa only [rlpEncodeBytesCopyTail,Nat.add_zero] using bounded
 | rStruct fields=>
  simp [RunBounded,rlpEncodeBytesCopyTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,
   rlpEncodeBytesCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atSrc,atLen,atHeader,
   wordOpHOL,valueIsWord]
 | nStruct name fields=>
  simp [RunBounded,rlpEncodeBytesCopyTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,
   rlpEncodeBytesCopyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atDst,atSrc,atLen,atHeader,
   wordOpHOL,valueIsWord]

/-- Complete original encoder for any bounded byte count. The source and
 destination may be unreadable; those executions terminate within the same bound. -/
theorem rlp_encode_bytes_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination source length : BitVec 64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word destination)))
 (atSrc : s.locals.lookup (ofString "src")=some (.val (.word source)))
 (atLen : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (code : s.code=originalRuntimeCode) (small : length.toNat≤2^62)
 (budget : rlpEncodeBytesSourceCost length.toNat≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) (rlpEncodeBytesSourceCost length.toNat) := by
 rw [ebBody_eq]
 change RunBounded s (.seq rlpEncodeBytesGuard (.decCall (ofString "h") .one (ofString "rlp_write_header")
  [.var .local (ofString "dst"),.const (128#64),.var .local (ofString "n")] rlpEncodeBytesCopyTail)) _
 have guardBound:=ProgBounded.straight rlpEncodeBytesGuard rfl s code (Nat.zero_le _)
 have restCost : 0+rlpEncodeBytesSourceCost length.toNat≤s.clock := by simpa using budget
 have composed:=RunBounded.seq (tail:=.decCall (ofString "h") .one (ofString "rlp_write_header")
   [.var .local (ofString "dst"),.const (128#64),.var .local (ofString "n")] rlpEncodeBytesCopyTail) guardBound restCost (by
  intro mid run installed ticks
  have localsKept (key : MlS) (avoid : avoidsLocal key rlpEncodeBytesGuard=true) : mid.locals.lookup key=s.locals.lookup key := by
   have frame:=evaluate_avoidsLocal_flowing key rlpEncodeBytesGuard avoid s (by rw [run];exact Or.inl rfl)
   rw [run] at frame;exact frame
  have dst := (localsKept (ofString "dst") rfl).trans atDst
  have src := (localsKept (ofString "src") rfl).trans atSrc
  have len := (localsKept (ofString "n") rfl).trans atLen
  have midCode:=installed.trans code
  have args : evalListHOLFinite mid (h:=fun a=>Classical.propDecidable (mid.memaddrs a))
   [.var .local (ofString "dst"),.const (128#64),.var .local (ofString "n")]=
   some [.val (.word destination),.val (.word (128#64)),.val (.word length)] := by
   simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,dst,len]
  apply RunBounded.decCall (name:=ofString "h") (function:=ofString "rlp_write_header") (shape:=.one)
   (continuation:=rlpEncodeBytesCopyTail) (bodyCost:=rlpWriterSourceCost) (tailCost:=length.toNat/32+length.toNat/8+11) args ticks
  intro body callee shape lookup
  have calleeBound:=ProgBounded.bodies_of_fun rlp_write_header_fun_bounded mid midCode (by
   unfold rlpEncodeBytesSourceCost at ticks;omega) _ _ _ _ lookup
  refine ⟨calleeBound,?_⟩
  intro value post returned remaining
  have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite mid callee) body
  rw [returned] at metadata
  apply rlp_encode_bytes_copy_tail_bounded _ destination source length value
  · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using dst
  · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using src
  · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using len
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact metadata.1.trans midCode
  · exact small
  · exact remaining)
 simpa only [Nat.zero_add] using composed
#print axioms rlp_encode_bytes_body_bounded
end InitECandidate.Runtime

import InitECandidate.Runtime.MptInsertIndexedCallBound
import InitECandidate.Runtime.MptSetIndexedAllocatedPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptSetInsertArguments : List (ExpHOL 64):=
 [.var .local (ofString "root"),.rfield 0 (.var .local (ofString "nk")),.rfield 1 (.var .local (ofString "nk")),
  .const 0,.var .local (ofString "vptr"),.var .local (ofString "vlen")]
def mptSetDeleteCondition : ExpHOL 64:=
 .cmp .notEqual (.const 0) (.op .or [.cmp .equal (.var .local (ofString "vptr")) (.const 0),
  .cmp .equal (.var .local (ofString "vlen")) (.const 0)])
def mptSetDeleteCall : ProgHOL 64:=
 match mptSetAt 2 with | .seq (.ite _ yes _) _=>yes | _=>.skip

theorem source_mpt_set_dispatch : mptSetAt 2=
 .seq (.ite mptSetDeleteCondition mptSetDeleteCall
  (.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_insert_node") mptSetInsertArguments)) (mptSetAt 3) :=rfl

theorem source_mpt_set_after_dispatch : mptSetAt 3=
 .seq (.store (.op .add [.var .local (ofString "m"),.const 0]) (.var .local (ofString "root"))) (.return (.const 0)) :=rfl

/-- The real insertion/deletion choice of indexed mpt_set selects the actual
bounded insertion call when both value fields are nonzero, then performs its
original root store and return. Invalid call/store outcomes are included. -/
theorem mpt_set_insert_dispatch_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier node key length valuePointer valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (nibbles : TrieNibbleRange s key length)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (pointerNonzero : valuePointer≠0#64) (lengthNonzero : valueLength≠0#64)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)+1≤s.clock) :
 RunBounded s (mptSetAt 2) (19*((2^64+203)+1)+1) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) mptSetInsertArguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word (0#64)),.val (.word valuePointer),.val (.word valueLength)] := by
  simp [mptSetInsertArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atRoot,atKey,atValue,atValueLength]
 have inserted:=mpt_insert_indexed_call_bounded s live extensions branches size mptSetInsertArguments (some (.local,ofString "root"))
  frontier node key length 0 valuePointer valueLength args world nibbles fullDomain nodeValid (by simp) capacity recordsBefore aligned keyExtent short code budget
 have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) mptSetDeleteCondition=
  some (.val (.word (0#64))) := by
  simp [mptSetDeleteCondition,evalHOLExact,evalListHOLExact,atValue,atValueLength,pointerNonzero,lengthNonzero,
   Compiler.Encoders.Asm.wordCmpHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
  rfl
 have choice : RunBounded s (.ite mptSetDeleteCondition mptSetDeleteCall
  (.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_insert_node") mptSetInsertArguments)) (19*((2^64+203)+1)+1) := by
  unfold RunBounded
  rw [evaluateHOLFiniteState_ite,condition]
  exact inserted
 rw [source_mpt_set_dispatch]
 refine RunBounded.seq (state:=s) (a:=19*((2^64+203)+1)+1) (b:=0) choice budget ?_
 intro next _ nextCode _
 exact ProgBounded.straight _ (by rw [source_mpt_set_after_dispatch];rfl) next (nextCode.trans code) (Nat.zero_le _)

#print axioms mpt_set_insert_dispatch_bounded
end InitECandidate.Runtime

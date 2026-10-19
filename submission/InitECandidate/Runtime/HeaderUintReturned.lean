import InitECandidate.Runtime.GuardOnlyFlow
import InitECandidate.Runtime.HeaderRlpFieldBound
import InitECandidate.Runtime.RlpItemBodyRange
import InitECandidate.Runtime.PanDecCallReturnedBodyScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def headerUintTailAt (index : Nat) : ProgHOL 64 := (statelessNext^[index]) (headerRlpFieldTail .uint)
def headerUintCheck (index : Nat) : ProgHOL 64 :=
  match headerUintTailAt index with | .seq check _ => check | _ => .skip

theorem source_header_uint_tail_zero : headerUintTailAt 0 = .seq (headerUintCheck 0) (headerUintTailAt 1) := rfl
theorem source_header_uint_tail_one : headerUintTailAt 1 = .seq (headerUintCheck 1) (headerUintTailAt 2) := rfl
theorem source_header_uint_tail_two : headerUintTailAt 2 = .seq (headerUintCheck 2) (headerUintTailAt 3) := rfl
theorem source_header_uint_tail_return : headerUintTailAt 3 =
    .return (.rstruct [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))]) := rfl

theorem header_uint_tail_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed : BitVec 64) (v : ValueHOL 64)
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (run : evaluateHOLFiniteState s (headerRlpFieldTail .uint) = (some (.returned v),post)) :
    v = .rStruct [.val (.word pointer),.val (.word length)] := by
  change evaluateHOLFiniteState s (headerUintTailAt 0) = _ at run
  rw [source_header_uint_tail_zero] at run
  have run1 := guard_only_seq_returned s post (headerUintCheck 0) (headerUintTailAt 1) rfl v run
  rw [source_header_uint_tail_one] at run1
  have run2 := guard_only_seq_returned s post (headerUintCheck 1) (headerUintTailAt 2) rfl v run1
  rw [source_header_uint_tail_two] at run2
  have run3 := guard_only_seq_returned s post (headerUintCheck 2) (headerUintTailAt 3) rfl v run2
  rw [source_header_uint_tail_return] at run3
  have returned : evaluateHOLFiniteState s
      (.return (.rstruct [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))])) =
      (some (.returned (.rStruct [.val (.word pointer),.val (.word length)])),emptyLocalsHOLFinite s) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atItem,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [returned] at run3
  simpa using (Prod.mk.inj run3).1.symm

/-- The actual unsigned header-field helper returns a typed pointer/length
pair inside its parsed input; the contract is extracted from its RLP execution. -/
theorem header_uint_body_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (v : ValueHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) headerRlpFieldArguments =
      some [.val (.word pointer),.val (.word length)])
    (code : s.code = originalRuntimeCode) (fits : pointer.toNat + length.toNat < 2^64)
    (lengthFits : length.toNat + 9 < 2^64) (ticks : 12 ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_hdr_uint_field) = (some (.returned v),post)) :
    ∃ outputPointer outputLength : BitVec 64,
      v = .rStruct [.val (.word outputPointer),.val (.word outputLength)] ∧
      pointer.toNat ≤ outputPointer.toNat ∧ outputPointer.toNat + outputLength.toNat ≤ pointer.toNat + length.toNat ∧
      outputPointer.toNat + outputLength.toNat < 2^64 ∧ outputLength.toNat ≤ length.toNat := by
  change evaluateHOLFiniteState s (sourceFunctionBody (headerRlpFieldDeclaration .uint)) = _ at run
  rw [source_header_rlp_field] at run
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite s callee
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  obtain ⟨item,bodyPost,ready,output,bodyRun,_,_,_,_,_,tail,_⟩ :=
    evaluate_decCall_returned_body_scope s post (ofString "it") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) headerRlpFieldArguments _
      (sourceFunctionBody Guest.guestFn_rlp_item) (headerRlpFieldTail .uint) callee v args lookup run
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨kind,outPointer,outLength,consumed,itemShape,endBound,noWrap,startBound⟩ :=
    rlpItem_body_return_range entry bodyPost pointer length item atPointer atLength code (by change 11 ≤ s.clock - 1; omega)
      fits lengthFits bodyRun
  have valueEq := header_uint_tail_returned (setVarHOLFinite (ofString "it") item ready) output kind outPointer outLength consumed v
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,itemShape]) tail
  exact ⟨outPointer,outLength,valueEq,startBound,endBound,noWrap,by omega⟩

#print axioms header_uint_tail_returned
#print axioms header_uint_body_returned
end InitECandidate.Runtime

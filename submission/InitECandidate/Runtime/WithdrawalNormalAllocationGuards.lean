import InitECandidate.Runtime.HeaderWithdrawalLoopBody
import InitECandidate.Runtime.HeapDeclarationReturnedContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completing actual slice iteration proves its own allocation
request and resulting cap. No room for this or a future iteration is assumed. -/
theorem wd_slice_normal_allocation_guards {F : Type} (t : PanSemStateFiniteExact 64 F)
 (heap argumentWord : BitVec 64)
 (atHeap : t.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (code : t.code=originalRuntimeCode)
 (args : evalListHOLFinite t (h:=fun a=>Classical.propDecidable (t.memaddrs a))
  [.op .add [.load .one (.op .add [.var .local (ofString "pl"),.const (48#64)]),
   .panop .mul [.var .local (ofString "i"),.const (44#64)]]]=
   some [.val (.word argumentWord)])
 (normal : (evaluateHOLFiniteState t wdSliceLoopBody).1=none) :
 (64#64)≤(33806089496 : BitVec 64)-heap ∧(allocationEnd heap 64).toNat≤33806089496 := by
 obtain ⟨first,second,output,run,shape⟩:=wd_slice_step_outcome t argumentWord code args normal
 rw [source_rlpEncodeWithdrawal_body,rlpEncodeWithdrawal_eq] at run
 change evaluateHOLFiniteState (callEntryStateHOLFinite t (wdEncoderCallee argumentWord))
  (.decCall (ofString "buf") .one (ofString "alloc") [.const (64#64)] wdDecP)=_ at run
 have argument : evalListHOLFinite (callEntryStateHOLFinite t (wdEncoderCallee argumentWord))
  (h:=fun a=>Classical.propDecidable (t.memaddrs a)) [.const (64#64)]=some [.val (.word (64#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
 obtain ⟨_,_,_,_,_,_,_,_,_,request,finish⟩:=heap_declaration_returned_contract
  (callEntryStateHOLFinite t (wdEncoderCallee argumentWord)) output (ofString "buf") (.const (64#64))
  wdDecP heap 64 (.rStruct [.val (.word first),.val (.word second)]) argument atHeap code run
 exact ⟨request,finish⟩

#print axioms wd_slice_normal_allocation_guards
end InitECandidate.Runtime

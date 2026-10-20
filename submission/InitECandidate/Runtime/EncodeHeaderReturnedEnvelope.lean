import InitECandidate.Runtime.EncodeHeaderFirstReturned
import InitECandidate.Runtime.AllocationDeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- An actual successful original header encoder returns its real two-word
encoding with length bounded by the concrete domain fence. -/
theorem encode_header_returned_envelope {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (header heap length : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atH : s.locals.lookup (ofString "h")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_encode_header)=(some (.returned value),post)) :
 ∃start encodedLength : BitVec 64,value=.rStruct [.val (.word start),.val (.word encodedLength)] ∧
 heap.toNat≤start.toNat ∧encodedLength.toNat≤DF := by
 rw [sourceFunctionBody_eq_structural] at run
 have stage0 : encodeHeaderAt 0=.decCall (ofString "buf") .one (ofString "alloc") [.const 1024] (encodeHeaderAt 1) := rfl
 change evaluateHOLFiniteState s (encodeHeaderAt 0)=_ at run
 rw [stage0] at run
 obtain ⟨ready,output,tailRun,locals,memory,installed,domain,globals,nextCap,covers,nextAligned,_⟩:=
  allocation_declaration_returned s post (ofString "buf") (.const 1024) (encodeHeaderAt 1) heap 1024 value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code atHeap heapCap run
 let nextHeap:=allocationEnd heap (1024#64)
 have nextCapBound : nextHeap.toNat≤33806089496 := nextCap
 have heapLow : heap.toNat≤nextHeap.toNat := by change heap.toNat+1024≤nextHeap.toNat at covers;omega
 have watchedNat : (header+136).toNat=header.toNat+136 := by
  rw [BitVec.toNat_add];apply Nat.mod_eq_of_lt;change header.toNat+136<2^64;omega
 have cursorNat : (heap+9).toNat=heap.toNat+9 := by
  rw [BitVec.toNat_add];apply Nat.mod_eq_of_lt;change heap.toNat+9<2^64;omega
 have stage1 : encodeHeaderAt 1=.dec (ofString "p") .one
  (.op .add [.var .local (ofString "buf"),.const 9]) (encodeHeaderAt 2) := rfl
 rw [stage1] at tailRun
 obtain ⟨initial,inner,evaluated,bodyRun,_⟩:=dec_returned_state tailRun
 have buffer : ready.locals.lookup (ofString "buf")=some (.val (.word heap)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have initialEq : initial=.val (.word (heap+9)) := by
  have exactEval : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
   (.op .add [.var .local (ofString "buf"),.const 9])=some (.val (.word (heap+9))) := by
   simp [evalHOLExact,evalListHOLExact,buffer,wordOpHOL,wordOp,valueIsWord,valueWord]
  exact Option.some.inj (evaluated.symm.trans exactEval)
 subst initial
 let entered:=setVarHOLFinite (ofString "p") (.val (.word (heap+9))) ready
 have valid : EncodeHeaderPrefixInvariant entered header nextHeap heap (header+136) length DF := by
  constructor
  · exact installed.trans code
  · change Fence ready.memaddrs DF;rw [domain];exact fence
  · change (ready.locals.update (ofString "p",.val (.word (heap+9)))).lookup (ofString "h")=_
    rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atH
  · change ready.globals.lookup (ofString "heap_ptr")=_
    rw [globals];simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nextHeap]
  · change ready.memory (header+136)=_;rw [memory];exact atLength
  · refine ⟨heap+9,?_,?_,?_⟩
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [cursorNat];omega
    · rw [cursorNat];change heap.toNat+1024≤nextHeap.toNat at covers;omega
 have enteredBuf : entered.locals.lookup (ofString "buf")=some (.val (.word heap)) := by
  simpa (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using buffer
 have enteredFloor : EncodeHeaderCursorLower entered (heap.toNat+9) := by
  intro cursor atCursor
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at atCursor
  subst cursor
  change heap.toNat+9≤(heap+9).toNat
  rw [cursorNat]
 exact encode_header_first_returned entered inner value header nextHeap heap length heap DF valid cap nextCap heapFence
  aligned (by rw [watchedNat];omega) heapLow enteredBuf (by omega) enteredFloor bodyRun
#print axioms encode_header_returned_envelope
end InitECandidate.Runtime

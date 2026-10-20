import InitECandidate.Runtime.EncodeHeaderFromPlanReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem encode_header_first_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (header heap lo length buffer : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (atBuf : s.locals.lookup (ofString "buf")=some (.val (.word buffer))) (bufferLow : 8≤buffer.toNat)
 (cursorLow : EncodeHeaderCursorLower s (buffer.toNat+9))
 (run : evaluateHOLFiniteState s (encodeHeaderAt 2)=(some (.returned value),post)) :
 ∃start encodedLength : BitVec 64,value=.rStruct [.val (.word start),.val (.word encodedLength)] ∧
 buffer.toNat≤start.toNat ∧encodedLength.toNat≤DF := by
 have stage : encodeHeaderAt 2=.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
  [.var .local (ofString "p"),encodeHeaderPrefixField 8,.const 32] (encodeHeaderAt 3) := rfl
 rw [stage] at run
 obtain ⟨values,body,callee,shape,returned,bodyPost,ready,output,args,lookup,calleeRun,locals,memory,globals,clock,domain,endian,installed,tailRun,_⟩:=
  encode_header_returned_declaration_context s post _ _ _ _ _ value run
 obtain ⟨dst,atP,low,high⟩:=valid.cursor
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (encodeHeaderPrefixField 8) with
 | none=>
  simp only [evalListHOLFinite_eq_toExact,evalListHOLExact] at args
  rw [evaluated] at args
  simp at args
 | some input=>
  have actual : values=[.val (.word dst),input,.val (.word (32#64))] := by
   simp only [evalListHOLFinite_eq_toExact,evalListHOLExact] at args
   rw [evaluated] at args
   simp [evalHOLExact,atP] at args
   exact args.symm
  subst values
  have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_bytes") _ _ body _ shape _ callee
   (by rw [valid.code];exact originalRuntimeCode_rlpEncodeBytes_lookup) lookup
  subst same
  rw [valid.code] at lookup
  have bindings:=callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
  let entry:=callEntryStateHOLFinite s callee
  have framed:=encode_header_bytes_body_returned_frame entry bodyPost dst 32 lo (header+136) DF returned
   valid.code valid.fence cap aligned below low high
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]) calleeRun
  obtain ⟨written,rfl,fits⟩:=framed.1
  let declared:=setVarHOLFinite (ofString "w") (.val (.word written)) ready
  have declaredP : declared.locals.lookup (ofString "p")=some (.val (.word dst)) := by
   simp only [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   rw [locals];simpa (config:={decide:=true}) using atP
  have declaredW : declared.locals.lookup (ofString "w")=some (.val (.word written)) := by
   simp [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have increment:=encode_header_cursor_increment declared dst written DF cap declaredP declaredW fits
  let next:=setVarHOLFinite (ofString "p") (.val (.word (dst+written))) declared
  have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
  rw [calleeRun] at metadata
  have nextValid : EncodeHeaderPrefixInvariant next header heap lo (header+136) length DF := by
   constructor
   · change ready.code=originalRuntimeCode;rw [installed];exact metadata.1.trans valid.code
   · change Fence ready.memaddrs DF;rw [domain,metadata.2.1];exact valid.fence
   · change (ready.locals.update (ofString "w",.val (.word written)) |>.update (ofString "p",.val (.word (dst+written)))).lookup (ofString "h")=_
     rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using valid.atH
   · change ready.globals.lookup (ofString "heap_ptr")=_;rw [globals,framed.2.2];exact valid.atHeap
   · change ready.memory (header+136)=_;rw [memory,framed.2.1];exact valid.atLength
   · exact ⟨dst+written,(by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),(by rw [increment.2];omega),(by rw [increment.2];exact fits)⟩
  have nextBuf : next.locals.lookup (ofString "buf")=some (.val (.word buffer)) := by
   simp only [next,declared,setVarHOLFinite]
   rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atBuf
  have nextLow : EncodeHeaderCursorLower next (buffer.toNat+9) := by
   intro cursor atCursor
   simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at atCursor
   subst cursor
   have oldLow:=cursorLow dst atP
   rw [increment.2];omega
  have stage3 : encodeHeaderAt 3=.seq encodeHeaderPrefixIncrement (encodeHeaderAt 4) := rfl
  rw [stage3,evaluateHOLFiniteState_seq_line780] at tailRun
  dsimp only [encodeHeaderPrefixIncrement] at tailRun
  rw [increment.1] at tailRun
  exact encode_header_from_plan_returned next output value header heap lo length buffer DF
   nextValid cap heapCap heapFence aligned below loHeap nextBuf bufferLow nextLow tailRun
#print axioms encode_header_first_returned
end InitECandidate.Runtime

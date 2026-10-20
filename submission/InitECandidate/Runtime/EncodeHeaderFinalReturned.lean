import InitECandidate.Runtime.EncodeHeaderFixedReturned
import InitECandidate.Runtime.EncGenPrepGD
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual final payload/header-length construction returns a bounded encoded
length. Its real pure length callee returns at most nine bytes. -/
theorem encode_header_final_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (cursor buffer : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (atP : s.locals.lookup (ofString "p")=some (.val (.word cursor)))
 (atBuf : s.locals.lookup (ofString "buf")=some (.val (.word buffer)))
 (bufferLow : 8≤buffer.toNat) (cursorLow : buffer.toNat+9≤cursor.toNat) (cursorHigh : cursor.toNat≤DF+8)
 (run : evaluateHOLFiniteState s (encodeHeaderAt 45)=(some (.returned value),post)) :
 ∃start length : BitVec 64,value=.rStruct [.val (.word start),.val (.word length)] ∧
 buffer.toNat≤start.toNat ∧start.toNat+length.toNat=cursor.toNat ∧length.toNat≤DF := by
 have bufferAdd : (buffer+9).toNat=buffer.toNat+9 := by
  rw [BitVec.toNat_add];apply Nat.mod_eq_of_lt;change buffer.toNat+9<2^64;omega
 let payload:=cursor-(buffer+9)
 have payloadNat : payload.toNat=cursor.toNat-(buffer.toNat+9) := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [bufferAdd];exact cursorLow)),bufferAdd]
 have stage45 : encodeHeaderAt 45=.dec (ofString "payload_len") .one
  (.op .sub [.var .local (ofString "p"),.op .add [.var .local (ofString "buf"),.const 9]]) (encodeHeaderAt 46) := rfl
 rw [stage45] at run
 obtain ⟨initial,inner,evaluated,bodyRun,_⟩:=dec_returned_state run
 have initialEq : initial=.val (.word payload) := by
  have exactEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
   (.op .sub [.var .local (ofString "p"),.op .add [.var .local (ofString "buf"),.const 9]])=some (.val (.word payload)) := by
   simp [payload,evalHOLExact,evalListHOLExact,atP,atBuf,wordOpHOL,wordOp,valueIsWord,valueWord]
  exact Option.some.inj (evaluated.symm.trans exactEval)
 subst initial
 let declared:=setVarHOLFinite (ofString "payload_len") (.val (.word payload)) s
 have declaredCode : declared.code=originalRuntimeCode := code
 have atPayload : declared.locals.lookup (ofString "payload_len")=some (.val (.word payload)) := by
  simp [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have stage46 : encodeHeaderAt 46=.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
  [.var .local (ofString "payload_len")] (encodeHeaderAt 47) := rfl
 rw [stage46] at bodyRun
 obtain ⟨values,body,callee,shape,returned,bodyPost,ready,output,args,lookup,calleeRun,locals,memory,globals,clock,domain,endian,installed,tailRun,_⟩:=
  encode_header_returned_declaration_context declared inner _ _ _ _ _ value bodyRun
 have argsEq : values=[.val (.word payload)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPayload] at args
  exact args.symm
 subst values
 have same:=lookupCodeHOLFinite_installed_body declared.code.lookup (ofString "rlp_list_header_len") _ _ body _ shape _ callee
  (by rw [declaredCode];exact originalRuntimeCode_rlpListHeaderLen_lookup) lookup
 subst same
 rw [declaredCode] at lookup
 have bindings:=callee_eq originalRuntimeCode_rlpListHeaderLen_lookup lookup
 let entry:=callEntryStateHOLFinite declared callee
 have dom : DomD entry.memaddrs entry.be entry := ⟨(by intro address present;have bound:=fence address present;omega),rfl,rfl⟩
 have spec:=listHeaderLen_spec (D:=entry.memaddrs) (B:=entry.be) (A:=fun _=>True) (w:=0) payload
 have actual:=spec F entry code dom trivial (by intro name impossible;exact impossible.elim) entry.globals rfl
  (by simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE])
 obtain ⟨ga,_,headerWord,wordEq,headerSmall⟩:=actual.2.2.2.1 returned (by rw [calleeRun])
 subst returned
 let headed:=setVarHOLFinite (ofString "hl") (.val (.word headerWord)) ready
 have headedBuf : headed.locals.lookup (ofString "buf")=some (.val (.word buffer)) := by
  simp only [headed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [locals];simpa (config:={decide:=true}) [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atBuf
 have headedPayload : headed.locals.lookup (ofString "payload_len")=some (.val (.word payload)) := by
  simp only [headed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [locals];simpa (config:={decide:=true}) [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPayload
 have headedHeader : headed.locals.lookup (ofString "hl")=some (.val (.word headerWord)) := by
  simp [headed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have stage47 : encodeHeaderAt 47=.dec (ofString "start") .one
  (.op .sub [.op .add [.var .local (ofString "buf"),.const 9],.var .local (ofString "hl")]) (encodeHeaderAt 48) := rfl
 rw [stage47] at tailRun
 obtain ⟨startValue,lastPost,startEval,lastRun,_⟩:=dec_returned_state tailRun
 let start:=buffer+9-headerWord
 have startEq : startValue=.val (.word start) := by
  have exactEval : @evalHOLExact 64 F _ headed.toExact (fun a=>Classical.propDecidable (headed.memaddrs a))
   (.op .sub [.op .add [.var .local (ofString "buf"),.const 9],.var .local (ofString "hl")])=some (.val (.word start)) := by
   simp [start,evalHOLExact,evalListHOLExact,headedBuf,headedHeader,wordOpHOL,wordOp,valueIsWord,valueWord]
  exact Option.some.inj (startEval.symm.trans exactEval)
 subst startValue
 let started:=setVarHOLFinite (ofString "start") (.val (.word start)) headed
 have stage48 : encodeHeaderAt 48=.seq
  (.call (some (none,none)) (ofString "rlp_encode_list_header") [.var .local (ofString "start"),.var .local (ofString "payload_len")])
  (encodeHeaderAt 49) := rfl
 rw [stage48] at lastRun
 obtain ⟨finished,callRun,returnRun⟩:=encode_header_seq_returned_of_no_return started lastPost _ _ value
  ((evaluate_handlerFree_call_control started _ _ _).2.2) lastRun
 have kept:=evaluate_discard_call_success_locals started (ofString "rlp_encode_list_header") _ (by rw [callRun])
 rw [callRun] at kept
 have finishStart : finished.locals.lookup (ofString "start")=some (.val (.word start)) := by
  rw [kept];simp [started,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have finishPayload : finished.locals.lookup (ofString "payload_len")=some (.val (.word payload)) := by
  rw [kept];simpa (config:={decide:=true}) [started,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using headedPayload
 have finishHeader : finished.locals.lookup (ofString "hl")=some (.val (.word headerWord)) := by
  rw [kept];simpa (config:={decide:=true}) [started,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using headedHeader
 have actualReturn : value=.rStruct [.val (.word start),.val (.word (payload+headerWord))] := by
  have result:=(Prod.mk.inj returnRun).1
  change (evaluateHOLFiniteState finished (.return (.rstruct [.var .local (ofString "start"),
   .op .add [.var .local (ofString "payload_len"),.var .local (ofString "hl")]]))).1=some (.returned value) at result
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,finishStart,finishPayload,finishHeader,
   wordOpHOL,wordOp,valueIsWord,valueWord] at result
  split at result
  · simpa using result.symm
  · simp at result
 have startNat : start.toNat=buffer.toNat+9-headerWord.toNat := by
  dsimp only [start]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [bufferAdd];omega)),bufferAdd]
 have lengthNat : (payload+headerWord).toNat=payload.toNat+headerWord.toNat := by
  rw [BitVec.toNat_add];apply Nat.mod_eq_of_lt
  rw [payloadNat];omega
 refine ⟨start,payload+headerWord,actualReturn,?_,?_,?_⟩
 · rw [startNat];omega
 · rw [startNat,lengthNat,payloadNat];omega
 · rw [lengthNat,payloadNat];omega
#print axioms encode_header_final_returned
end InitECandidate.Runtime

import InitECandidate.Runtime.MptNibbleUnsecuredBodyReturned
import InitECandidate.Runtime.KeyNibbleBodyWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual indexed-key conversion preserves all older heap words. The
real allocator guard supplies its extent; no caller-space, input-readability,
successful-store or minimum-fuel premise is used. -/
theorem mpt_nibble_unsecured_tail_returned_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (key length pointer : BitVec 64) (value : ValueHOL 64)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (short : length.toNat≤9) (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptNibbleUnsecuredTail=(some (.returned value),post)) :
 ∀watched : BitVec 64,watched.toNat<pointer.toNat→post.memory watched=s.memory watched := by
 rw [source_mpt_nibble_unsecured_tail] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.panop .mul [.const 2,.var .local (ofString "klen")]]=some [.val (.word (2#64*length))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
 obtain ⟨allocationPost,output,tailRun,scope,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "nb2") _ _ pointer (2#64*length) value args atHeap code run
 have sizeNat : (2#64*length).toNat=2*length.toNat := by
  rw [BitVec.toNat_mul]
  change (2*length.toNat)%2^64=2*length.toNat
  exact Nat.mod_eq_of_lt (by omega)
 have extent:=allocationGuard_sum_bound pointer (2#64*length) capped request
 rw [sizeNat] at extent
 let next:=setVarHOLFinite (ofString "nb2") (.val (.word pointer)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState next (.seq _ mptNibbleUnsecuredReturn)=(some (.returned value),output) at tailRun
 obtain ⟨converted,conversionRun,returnRun⟩:=encode_header_seq_returned_of_no_return next output _ _ value
  (fun v=>(evaluate_handlerFree_call_control next _ _ _).2.2 v) tailRun
 have nextKey : next.locals.lookup (ofString "key")=some (.val (.word key)) := by
  simpa (config:={decide:=true}) [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKey
 have nextLength : next.locals.lookup (ofString "klen")=some (.val (.word length)) := by
  simpa (config:={decide:=true}) [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 have nextOutput : next.locals.lookup (ofString "nb2")=some (.val (.word pointer)) := by
  simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have conversionArgs : evalListHOLFinite next (h:=fun a=>Classical.propDecidable (next.memaddrs a))
  [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]=
  some [.val (.word key),.val (.word length),.val (.word pointer)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,nextKey,nextLength,nextOutput]
 have returnMemory:=evaluate_readOnly_memory mptNibbleUnsecuredReturn rfl converted
 rw [returnRun] at returnMemory
 intro watched before
 have separated : ∀offset : Nat,offset<2*length.toNat→
  watched≠panByteAlignHOL (pointer+BitVec.ofNat 64 offset) := by
  intro offset inside equal
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset := by
   rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have addNat : (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := by
   rw [BitVec.toNat_add_of_lt (by rw [offsetNat];omega),offsetNat]
  have alignedNat:=panByteAlign_toNat64 (pointer+BitVec.ofNat 64 offset)
  rw [←equal,addNat] at alignedNat
  have base:=Nat.mod_add_div pointer.toNat 8
  have sum:=Nat.mod_add_div (pointer.toNat+offset) 8
  have rem:=Nat.mod_lt (pointer.toNat+offset) (by decide : 0<8)
  omega
 have convertedMemory:=evaluate_keyNibble_call_word_frame next _ _ _ key length pointer watched
  (by omega) (installed.trans code) conversionArgs separated
 rw [conversionRun] at convertedMemory
 rw [scope]
 exact (congrFun returnMemory watched).trans (convertedMemory.trans (congrFun memory watched))

theorem mpt_nibble_unsecured_body_returned_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (value : ValueHOL 64)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0)
 (short : length.toNat≤9) (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mpt_nibble_key)=(some (.returned value),post)) :
 ∀watched : BitVec 64,watched.toNat<pointer.toNat→post.memory watched=s.memory watched :=
 mpt_nibble_unsecured_tail_returned_memory s post key length pointer value atKey atLength atHeap short capped aligned code
  (mpt_nibble_unsecured_returned_tail s post table value atTable unsecured run)

#print axioms mpt_nibble_unsecured_tail_returned_memory
#print axioms mpt_nibble_unsecured_body_returned_memory
end InitECandidate.Runtime

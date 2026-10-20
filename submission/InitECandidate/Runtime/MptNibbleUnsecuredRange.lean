import InitECandidate.Runtime.MptNibbleUnsecuredMemoryFrame
import InitECandidate.Runtime.KeyToNibblesNormalRangeAnyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The expanded heap domain covers byte reads in a concrete bounded interval. -/
theorem mpt_nibble_interval_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
 (base : BitVec 64) (size : Nat) (extent : base.toNat+size≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (offset : Nat) (inside : offset<size) :
 s.memaddrs (panByteAlignHOL (base+BitVec.ofNat 64 offset)) := by
 have offsetNat : (BitVec.ofNat 64 offset).toNat=offset := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
 have addNat : (base+BitVec.ofNat 64 offset).toNat=base.toNat+offset := by
  rw [BitVec.toNat_add_of_lt (by rw [offsetNat];omega),offsetNat]
 apply fullDomain
 rw [panByteAlign_toNat64,addNat]
 have down:=Nat.div_mul_le_self (base.toNat+offset) 8
 omega

/-- A completed actual unsecured conversion produces valid nibble values.
The actual successful allocation earns output extent, and clock extension
replays the same conversion; no space or minimum-fuel premise is assumed. -/
theorem mpt_nibble_unsecured_tail_returned_range {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (key length pointer : BitVec 64) (value : ValueHOL 64)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (short : length.toNat≤9) (capped : pointer.toNat≤33806089496)
 (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptNibbleUnsecuredTail=(some (.returned value),post)) :
 TrieNibbleRange post pointer (2*length) := by
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
 have nextDomain : ∀address : BitVec 64,address.toNat<33806089496→next.memaddrs address := by
  intro address inside
  change allocationPost.memaddrs address
  rw [domain]
  exact fullDomain address inside
 have sourceDomain : ∀offset : Nat,offset<length.toNat→next.memaddrs (panByteAlignHOL (key+BitVec.ofNat 64 offset)) :=
  fun offset inside=>mpt_nibble_interval_domain next key length.toNat (by omega) nextDomain offset inside
 have outputDomain : ∀offset : Nat,offset<2*length.toNat→next.memaddrs (panByteAlignHOL (pointer+BitVec.ofNat 64 offset)) :=
  fun offset inside=>mpt_nibble_interval_domain next pointer (2*length.toNat) extent nextDomain offset inside
 have range:=key_to_nibbles_normal_range_any_clock next converted _ _ _ key pointer length
  (by omega) (installed.trans code) conversionArgs sourceDomain outputDomain conversionRun
 have returnMemory:=evaluate_readOnly_memory mptNibbleUnsecuredReturn rfl converted
 have returnMetadata:=evaluateHOLFiniteState_metadata converted mptNibbleUnsecuredReturn
 rw [returnRun] at returnMemory returnMetadata
 have outputRange:=range.after_frame returnMemory returnMetadata.2.1 returnMetadata.2.2.1
 rw [scope]
 exact outputRange.after_frame rfl rfl rfl

theorem mpt_nibble_unsecured_body_returned_range {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (value : ValueHOL 64)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0)
 (short : length.toNat≤9) (capped : pointer.toNat≤33806089496)
 (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mpt_nibble_key)=(some (.returned value),post)) :
 TrieNibbleRange post pointer (2*length) :=
 mpt_nibble_unsecured_tail_returned_range s post key length pointer value atKey atLength atHeap short capped keyBefore
  fullDomain code (mpt_nibble_unsecured_returned_tail s post table value atTable unsecured run)

#print axioms mpt_nibble_interval_domain
#print axioms mpt_nibble_unsecured_tail_returned_range
#print axioms mpt_nibble_unsecured_body_returned_range
end InitECandidate.Runtime

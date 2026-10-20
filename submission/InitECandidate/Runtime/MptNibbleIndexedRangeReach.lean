import InitECandidate.Runtime.MptNibbleUnsecuredDeclarationReach
import InitECandidate.Runtime.MptNibbleUnsecuredRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual installed indexed-key declaration supplies valid nibble values
alongside its exact allocation and old-memory frame, or terminates in nine
source clocks. Buffer readability is derived from owned intervals and the
expanded arena; successful allocation is not assumed. -/
theorem mpt_nibble_indexed_range_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (table key length pointer : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word table),.val (.word key),.val (.word length)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (short : length.toNat≤9)
 (capped : pointer.toNat≤33806089496) (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 Reaches s (.decCall name (.comb [.one,.one]) (ofString "mpt_nibble_key") arguments tail)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next name pointer length ∧
   TrieNibbleRange next pointer (2*length)) 9 tail := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((HolFiniteMapExact.empty.update (ofString "m",.val (.word table))).update
   (ofString "key",.val (.word key))).update (ofString "klen",.val (.word length))
 let entry:=callEntryStateHOLFinite s callee
 have installed : s.code.lookup (ofString "mpt_nibble_key")=some
  ([(ofString "m",.one),(ofString "key",.one),(ofString "klen",.one)],sourceFunctionBody Guest.guestFn_mpt_nibble_key,.comb [.one,.one]) := by
  rw [code];exact originalRuntimeCode_mptNibbleKey_lookup
 have lookup:=pan_three_value_lookup_shape s.code.lookup (ofString "mpt_nibble_key")
  (ofString "m") (ofString "key") (ofString "klen") (sourceFunctionBody Guest.guestFn_mpt_nibble_key)
  (.comb [.one,.one]) (.word table) (.word key) (.word length) (by decide) (by decide) (by decide) installed
 have tableLocal : entry.locals.lookup (ofString "m")=some (.val (.word table)) := by
  simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have keyLocal : entry.locals.lookup (ofString "key")=some (.val (.word key)) := by
  simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have lengthLocal : entry.locals.lookup (ofString "klen")=some (.val (.word length)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_mpt_nibble_key) 8 :=
  (mpt_nibble_unsecured_body_bounded entry table key length pointer tableLocal keyLocal lengthLocal
   atHeap unsecured (by omega) code (by change 1+1+(length.toNat/4+4)≤s.clock-1;omega)).weaken (by omega)
 apply bounded_decCall_reaches s name (ofString "mpt_nibble_key") (.comb [.one,.one]) (.comb [.one,.one])
  arguments _ _ tail callee 8 _ args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,globals,request,finish,domain,endian,keptCode⟩:=mpt_nibble_unsecured_body_returned entry post
  table key length pointer value tableLocal keyLocal lengthLocal atHeap unsecured code run
 have range:=mpt_nibble_unsecured_body_returned_range entry post table key length pointer value
  tableLocal keyLocal lengthLocal atHeap unsecured short capped keyBefore fullDomain code run
 refine ⟨⟨?_,?_,globals,request,finish,domain,endian,keptCode,?_⟩,range.after_frame rfl rfl rfl⟩
 · simp [returned,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 · intro short capped aligned watched before
   exact mpt_nibble_unsecured_body_returned_memory entry post table key length pointer value
    tableLocal keyLocal lengthLocal atHeap unsecured short capped aligned code run watched before

#print axioms mpt_nibble_indexed_range_declaration_reaches
end InitECandidate.Runtime

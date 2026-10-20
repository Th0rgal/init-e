import InitECandidate.Runtime.MptNibbleUnsecuredBodyReturned
import InitECandidate.Runtime.OriginalMptNibbleKeyCode
import InitECandidate.Runtime.PanThreeValueLookupShape
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.MptNibbleUnsecuredMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def MptNibbleUnsecuredDeclarationReady {F : Type} (base next : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer length : BitVec 64) : Prop :=
 next.locals.lookup name=some (.rStruct [.val (.word pointer),.val (.word (2*length))]) ∧
 (∀key,key≠name→next.locals.lookup key=base.locals.lookup key) ∧
 next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer (2*length)))) ∧
 2*length≤(33806089496 : BitVec 64)-pointer ∧
 (allocationEnd pointer (2*length)).toNat≤33806089496 ∧
 next.memaddrs=base.memaddrs ∧next.be=base.be ∧next.code=base.code ∧
 (length.toNat≤9→pointer.toNat≤33806089496→pointer.toNat%8=0→
  ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched)

theorem MptNibbleUnsecuredDeclarationReady.before_memory {F : Type}
 {base next : PanSemStateFiniteExact 64 F} {name : MlS} {pointer length : BitVec 64}
 (ready : MptNibbleUnsecuredDeclarationReady base next name pointer length)
 (short : length.toNat≤9) (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0) :
 ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched := by
 rcases ready with ⟨_,_,_,_,_,_,_,_,memory⟩
 exact memory short capped aligned

/-- The actual installed two-result declaration reaches its continuation
with the real allocation pointer and doubled key length, or terminates within
the input-linear ceiling. No successful callee or caller-space premise. -/
theorem mpt_nibble_unsecured_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (table key length pointer : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word table),.val (.word key),.val (.word length)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (small : length.toNat+4<2^64)
 (code : s.code=originalRuntimeCode) (budget : (1+1+(length.toNat/4+4))+1≤s.clock) :
 Reaches s (.decCall name (.comb [.one,.one]) (ofString "mpt_nibble_key") arguments tail)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next name pointer length)
  ((1+1+(length.toNat/4+4))+1) tail := by
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
 have bounded:=mpt_nibble_unsecured_body_bounded entry table key length pointer tableLocal keyLocal lengthLocal
  atHeap unsecured small code (by change 1+1+(length.toNat/4+4)≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "mpt_nibble_key") (.comb [.one,.one]) (.comb [.one,.one])
  arguments _ _ tail callee (1+1+(length.toNat/4+4)) _ args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,globals,request,finish,domain,endian,keptCode⟩:=mpt_nibble_unsecured_body_returned entry post
  table key length pointer value tableLocal keyLocal lengthLocal atHeap unsecured code run
 refine ⟨?_,?_,globals,request,finish,domain,endian,keptCode,?_⟩
 · simp [returned,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 · intro short capped aligned watched before
   exact mpt_nibble_unsecured_body_returned_memory entry post table key length pointer value
    tableLocal keyLocal lengthLocal atHeap unsecured short capped aligned code run watched before

#print axioms mpt_nibble_unsecured_declaration_reaches
end InitECandidate.Runtime

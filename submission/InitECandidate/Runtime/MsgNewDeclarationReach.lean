import InitECandidate.Runtime.MsgNewReturnedFrame
import InitECandidate.Runtime.MsgNewRuntimeBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.SystemMessageGasSetup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Facts derived at the actual returned heap-message declaration. -/
structure MsgNewReady {F : Type} (base : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
 (next : PanSemStateFiniteExact 64 F) : Prop where
 atMessage : next.locals.lookup (ofString "m")=some (.val (.word pointer))
 locals : ∀key,key≠ofString "m"→next.locals.lookup key=base.locals.lookup key
 code : next.code=base.code
 domain : next.memaddrs=base.memaddrs
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 176)))
 extent : pointer.toNat+176≤(allocationEnd pointer 176).toNat
 aligned : (allocationEnd pointer 176).toNat%8=0
 capped : (allocationEnd pointer 176).toNat≤33806089496
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched

/-- The message declaration reaches its real continuation, with the derived
message extent and old-memory frame, or rejects in 42 clocks. Positivity is
supplied by the real heap floor; no allocation reserve is required. -/
theorem msg_new_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
 (tail : ProgHOL 64) (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (positive : 0<pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (budget : 42≤s.clock) :
 Reaches s (.decCall (ofString "m") .one (ofString "msg_new") [] tail) (MsgNewReady s pointer) 42 tail := by
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some [] := rfl
 have installed : s.code.lookup (ofString "msg_new")=some ([],sourceFunctionBody Guest.guestFn_msg_new,.one) := by
  rw [code];exact originalRuntimeCode_msgNew_lookup
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "msg_new") []=
  some (sourceFunctionBody Guest.guestFn_msg_new,HolFiniteMapExact.empty,.one) := by
  exact pan_no_args_lookup s.code.lookup (ofString "msg_new") (sourceFunctionBody Guest.guestFn_msg_new) installed
 have bodyBound : RunBounded entry (sourceFunctionBody Guest.guestFn_msg_new) 41 := by
  obtain ⟨params,body,shape,original,bounded⟩:=msg_new_fun_bounded
  rw [originalRuntimeCode_msgNew_lookup] at original
  cases original
  exact bounded entry code (by change 41≤s.clock-1;omega)
 apply bounded_decCall_reaches s (ofString "m") (ofString "msg_new") .one .one [] []
  (sourceFunctionBody Guest.guestFn_msg_new) tail HolFiniteMapExact.empty 41 (MsgNewReady s pointer) args lookup budget bodyBound
 intro value post run checked
 obtain ⟨returned,globals,extent,newAligned,newCapped,_,domain,postCode⟩:=
  msg_new_returned_frame entry post pointer 0 value atHeap aligned capped code positive run
 let next:=setVarHOLFinite (ofString "m") value {post with locals:=s.locals}
 have result : MsgNewReady s pointer next := by
  constructor
  · simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,returned]
  · intro key different
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · exact postCode
  · exact domain
  · exact globals
  · exact extent
  · exact newAligned
  · exact newCapped
  · intro watched before
    exact (msg_new_returned_frame entry post pointer watched value atHeap aligned capped code before run).2.2.2.2.2.1
 exact result

theorem source_system_message_new : systemTransactionAt 8=
 .decCall (ofString "m") .one (ofString "msg_new") [] (systemTransactionAt 9) := rfl
#print axioms msg_new_declaration_reaches
#print axioms source_system_message_new
end InitECandidate.Runtime

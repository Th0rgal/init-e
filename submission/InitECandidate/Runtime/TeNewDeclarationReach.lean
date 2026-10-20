import InitECandidate.Runtime.TeNewReturnedFrame
import InitECandidate.Runtime.TeNewRuntimeBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.SystemMessageGasSetup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Facts derived at the actual returned transaction environment declaration. -/
structure TeNewReady {F : Type} (base : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
 (next : PanSemStateFiniteExact 64 F) : Prop where
 atEnvironment : next.locals.lookup (ofString "te")=some (.val (.word pointer))
 locals : ∀key,key≠ofString "te"→next.locals.lookup key=base.locals.lookup key
 code : next.code=base.code
 domain : next.memaddrs=base.memaddrs
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 200)))
 extent : pointer.toNat+200≤(allocationEnd pointer 200).toNat
 aligned : (allocationEnd pointer 200).toNat%8=0
 capped : (allocationEnd pointer 200).toNat≤33806089496
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched

/-- The transaction environment declaration reaches its real continuation, with the derived
environment extent and old-memory frame, or rejects in 66 clocks. Positivity is
supplied by the real heap floor; no allocation reserve is required. -/
theorem te_new_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
 (tail : ProgHOL 64) (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (positive : 0<pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (budget : 66≤s.clock) :
 Reaches s (.decCall (ofString "te") .one (ofString "te_new") [] tail) (TeNewReady s pointer) 66 tail := by
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some [] := rfl
 have installed : s.code.lookup (ofString "te_new")=some ([],sourceFunctionBody Guest.guestFn_te_new,.one) := by
  rw [code];exact originalRuntimeCode_teNew_lookup
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "te_new") []=
  some (sourceFunctionBody Guest.guestFn_te_new,HolFiniteMapExact.empty,.one) := by
  exact pan_no_args_lookup s.code.lookup (ofString "te_new") (sourceFunctionBody Guest.guestFn_te_new) installed
 have bodyBound : RunBounded entry (sourceFunctionBody Guest.guestFn_te_new) 65 := by
  obtain ⟨params,body,shape,original,bounded⟩:=te_new_fun_bounded
  rw [originalRuntimeCode_teNew_lookup] at original
  cases original
  exact bounded entry code (by change 65≤s.clock-1;omega)
 apply bounded_decCall_reaches s (ofString "te") (ofString "te_new") .one .one [] []
  (sourceFunctionBody Guest.guestFn_te_new) tail HolFiniteMapExact.empty 65 (TeNewReady s pointer) args lookup budget bodyBound
 intro value post run checked
 obtain ⟨returned,globals,extent,newAligned,newCapped,_,domain,postCode⟩:=
  te_new_returned_frame entry post pointer 0 value atHeap aligned capped code positive run
 let next:=setVarHOLFinite (ofString "te") value {post with locals:=s.locals}
 have result : TeNewReady s pointer next := by
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
    exact (te_new_returned_frame entry post pointer watched value atHeap aligned capped code before run).2.2.2.2.2.1
 exact result

theorem source_system_environment_new : systemTransactionAt 2=
 .decCall (ofString "te") .one (ofString "te_new") [] (systemTransactionAt 3) := rfl
#print axioms te_new_declaration_reaches
#print axioms source_system_environment_new
end InitECandidate.Runtime

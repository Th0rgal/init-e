import InitECandidate.Runtime.FrameOpenFreshDomain
import InitECandidate.Runtime.FrameNewDeclarationPhysicalSeed
import InitECandidate.Runtime.FrameOpenTailReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Whole original frame_open: capture the real parent, construct the actual
funded frame, then install an actual zeroed104-byte linked continuation. -/
theorem frame_open_whole_returned_physical_seed {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame parent previous kind message codePointer codeLength accessAddresses accessSlots empty gas stateGas : BitVec 64) (value : ValueHOL 64)
 (atParent : s.globals.lookup (ofString "ev")=some (.val (.word parent)))
 (atPrevious : s.globals.lookup (ofString "cur_cont")=some (.val (.word previous)))
 (atKind : s.locals.lookup (ofString "kind")=some (.val (.word kind)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty)))
 (frameLower : 280≤frame.toNat) (ordered : frame.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (beforeMessage : scratch.toNat≤message.toNat) (messageBound : message.toNat+176≤2^64)
 (messageDomain : ∀offset∈([112,120,152,160] : List (BitVec 64)),s.memaddrs (message+offset))
 (codeAt : s.memory (message+112)=.word codePointer) (lengthAt : s.memory (message+120)=.word codeLength)
 (addressesAt : s.memory (message+152)=.word accessAddresses) (slotsAt : s.memory (message+160)=.word accessSlots)
 (gasAt : s.memory (message+40)=.word gas) (stateGasAt : s.memory (message+48)=.word stateGas)
 (lengthBound : codeLength.toNat≤134217712) (sourceCode : s.code=originalRuntimeCode)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (run : evaluateHOLFiniteState s (frameOpenAt 0)=(some (.returned value),post)) :
 FrameNewPhysicalSeed post (scratchAllocationEnd scratch 280) scratch frame codePointer codeLength message := by
 have metadata:=evaluateHOLFiniteState_metadata s (frameOpenAt 0)
 rw [run] at metadata
 rw [source_frame_open_0] at run
 obtain ⟨captured,afterParent,capturedEval,parentRun,parentScope⟩:=funding_declaration_returned_context run
 have capturedEq : captured=.val (.word parent):=by simpa [evalHOLExact] using capturedEval.symm.trans atParent
 subst captured
 let first:=setVarHOLFinite (ofString "parent") (.val (.word parent)) s
 change evaluateHOLFiniteState first (frameOpenAt 1)=_ at parentRun
 rw [source_frame_open_1] at parentRun
 have args : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.var .local (ofString "msg")]=some [.val (.word message)] := by
  simp (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalListHOLFinite,evalListHOLExact,evalHOLExact,atMessage]
 have recordDomain : ∀offset : Nat,offset<280 → first.memaddrs (panByteAlignHOL (scratchAllocationEnd scratch 280+BitVec.ofNat 64 offset)) := by
  intro offset inside
  exact frame_open_fresh_scratch_domain s scratch 280 (by change 280≤scratch.toNat;omega) scratchCap fullDomain offset inside
 obtain ⟨bodyPost,output,frontier,tailRun,childScope,seed,funding,childStateGas,savedScratch,savedFrame,childGlobals,childLower,childUpper,childExtent,childMemory,childDomain,childEndian,childCode⟩:=frame_new_declaration_returned_physical_seed first afterParent (ofString "child") (.var .local (ofString "msg")) (frameOpenAt 2) scratch frame message codePointer codeLength accessAddresses accessSlots empty gas stateGas value args atScratch atFrame atEmpty ordered scratchCap beforeMessage messageBound messageDomain codeAt lengthAt addressesAt slotsAt gasAt stateGasAt lengthBound sourceCode recordDomain parentRun
 let child:=scratchAllocationEnd scratch 280
 let ready:=setVarHOLFinite (ofString "child") (.val (.word child)) {bodyPost with locals:=first.locals}
 have readyParent : ready.locals.lookup (ofString "parent")=some (.val (.word parent)) := by simp (config:={decide:=true}) [ready,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have readyPrevious : ready.globals.lookup (ofString "cur_cont")=some (.val (.word previous)) := by simpa (config:={decide:=true}) [ready,first,setVarHOLFinite,childGlobals,HolFiniteMapExact.lookup_update,FUPDATE] using atPrevious
 have readyKind : ready.locals.lookup (ofString "kind")=some (.val (.word kind)) := by simpa (config:={decide:=true}) [ready,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKind
 have readyMessage : ready.locals.lookup (ofString "msg")=some (.val (.word message)) := by simpa (config:={decide:=true}) [ready,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atMessage
 have readyChild : ready.locals.lookup (ofString "child")=some (.val (.word child)) := by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have readyScratch : ready.globals.lookup (ofString "scratch_ptr")=some (.val (.word frontier)) := by simp [ready,first,setVarHOLFinite,childGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
 have readyFrame : ready.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (allocationEnd frame 1024))) := by simp (config:={decide:=true}) [ready,first,setVarHOLFinite,childGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
 have frameCoverage : frame.toNat+1024≤(allocationEnd frame 1024).toNat:=allocationEnd_covers_noWrap frame 1024 (by change frame.toNat+1024+7<2^64;omega)
 have frontierCap : frontier.toNat≤33806089496:=by change frontier.toNat≤child.toNat at childUpper;change child.toNat+280≤scratch.toNat at childExtent;omega
 have readyFull : ∀address : BitVec 64,address.toNat<33806089496 → ready.memaddrs address := by intro address below;change bodyPost.memaddrs address;rw [childDomain];exact fullDomain address below
 have tailDomain : ∀offset : Nat,offset<104 → ready.memaddrs (panByteAlignHOL (scratchAllocationEnd frontier 104+BitVec.ofNat 64 offset)) := by
  intro offset inside
  apply frame_open_fresh_scratch_domain ready frontier 104 _ frontierCap readyFull offset inside
  change 104≤frontier.toNat
  omega
 obtain ⟨returned,tailGlobals,tailLower,tailExtent,_,linkParent,linkPrevious,linkKind,done,linkMessage,tailMemory,_,_,_⟩:=frame_open_tail_returned ready output frontier (allocationEnd frame 1024) parent previous kind message child value readyParent readyPrevious readyKind readyMessage readyChild readyScratch readyFrame childLower frontierCap (childCode.trans sourceCode) tailDomain tailRun
 have endpointMemory : post.memory=output.memory:=by rw [parentScope,childScope]
 have endpointGlobals : post.globals=output.globals:=by rw [parentScope,childScope]
 apply seed.after_upper_frame post
 intro watched above
 change child.toNat≤watched.toNat at above
 rw [endpointMemory,tailMemory watched (by change frontier.toNat≤child.toNat at childUpper;omega)]
 rfl
#print axioms frame_open_whole_returned_physical_seed
end InitECandidate.Runtime

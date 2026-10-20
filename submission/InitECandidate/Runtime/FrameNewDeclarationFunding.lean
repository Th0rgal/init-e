import InitECandidate.Runtime.OriginalFrameNewCode
import InitECandidate.Runtime.FrameOpenSource
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Execute and invert the actual installed frame_new call. Every constructor
fact comes from its original body, rather than a caller-provided callee contract. -/
theorem frame_new_declaration_returned_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64)
 (scratch frame message codePointer codeLength accessAddresses accessSlots empty gas stateGas : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word message)])
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty)))
 (ordered : frame.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (beforeMessage : scratch.toNat≤message.toNat) (messageBound : message.toNat+176≤2^64)
 (messageDomain : ∀offset∈([112,120,152,160] : List (BitVec 64)),s.memaddrs (message+offset))
 (codeAt : s.memory (message+112)=.word codePointer) (lengthAt : s.memory (message+120)=.word codeLength)
 (addressesAt : s.memory (message+152)=.word accessAddresses) (slotsAt : s.memory (message+160)=.word accessSlots)
 (gasAt : s.memory (message+40)=.word gas) (stateGasAt : s.memory (message+48)=.word stateGas)
 (lengthBound : codeLength.toNat≤134217712) (sourceCode : s.code=originalRuntimeCode)
 (recordDomain : ∀offset : Nat,offset<280 → s.memaddrs (panByteAlignHOL (scratchAllocationEnd scratch 280+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "frame_new") [argument] tail)=(some (.returned value),post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,∃frontier : BitVec 64,let record:=scratchAllocationEnd scratch 280
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word record)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 HasGasFunding bodyPost record (childFunding gas) ∧bodyPost.memory (record+72)=.word stateGas ∧
 bodyPost.memory (record+208)=.word scratch ∧bodyPost.memory (record+224)=.word frame ∧
 bodyPost.globals=(s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd frame 1024)))).update (ofString "scratch_ptr",.val (.word frontier)) ∧
 (allocationEnd frame 1024).toNat≤frontier.toNat ∧frontier.toNat≤record.toNat ∧record.toNat+280≤scratch.toNat ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → bodyPost.memory watched=s.memory watched) ∧
 bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 have installed : s.code.lookup (ofString "frame_new")=some ([(ofString "msg",.one)],sourceFunctionBody Guest.guestFn_frame_new,.one) := by rw [sourceCode];exact originalRuntimeCode_frameNew_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "msg",.val (.word message))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "frame_new") (ofString "msg") (sourceFunctionBody Guest.guestFn_frame_new) message installed
 obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "frame_new") .one .one [argument] [.val (.word message)] (sourceFunctionBody Guest.guestFn_frame_new) tail callee value args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have entryMessage : entry.locals.lookup (ofString "msg")=some (.val (.word message)) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [sourceFunctionBody_eq_structural] at bodyRun
 change evaluateHOLFiniteState entry (frameNewAt 0)=(some (.returned allocated),bodyPost) at bodyRun
 obtain ⟨frontier,allocatedEq,funding,gasValue,savedScratch,savedFrame,globals,lower,upper,extent,memory,domain,endian,code⟩:=frame_new_whole_returned_funding entry bodyPost scratch frame message codePointer codeLength accessAddresses accessSlots empty gas stateGas allocated entryMessage atScratch atFrame atEmpty ordered scratchCap beforeMessage messageBound messageDomain codeAt lengthAt addressesAt slotsAt gasAt stateGasAt lengthBound sourceCode recordDomain bodyRun
 subst allocated
 exact ⟨bodyPost,output,frontier,tailRun,postEq,funding,gasValue,savedScratch,savedFrame,globals,lower,upper,extent,memory,domain,endian,code⟩
#print axioms frame_new_declaration_returned_funding
end InitECandidate.Runtime

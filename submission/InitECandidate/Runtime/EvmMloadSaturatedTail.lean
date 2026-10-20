import InitECandidate.Runtime.EvmMloadReadTail
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Real saturation/read/push/PC suffix, with no input-read success premise. -/
theorem mload_saturated_tail_returned_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch frontier pc memoryBase sa sb sc sd : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (memoryDomain : s.memaddrs (current.address+24)) (memoryAt : s.memory (current.address+24)=.word memoryBase)
 (pcDomain : s.memaddrs (current.address+0)) (pcAt : s.memory (current.address+0)=.word pc)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base) (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 rw [source_mload_2] at run
 obtain ⟨body,output,tail,scope,memory,globals,installed,domain,endian⟩:=funding_sat_word_declaration_geometry s post (ofString "s") (.var .local (ofString "start")) (mloadAt 3) sa sb sc sd value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt]) code run
 let ready:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord sa sb sc sd))) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mloadAt 3)=_ at tail
 have readyMemory : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyCode : ready.code=s.code:=installed
 have valid : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=layout.after_memory readyMemory readyDomain
 obtain ⟨zero,funding⟩:=mload_read_tail_returned_funding ready output upper current ancestors valid base index capacity scratch frontier pc memoryBase (evmSatWord sa sb sc sd) value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by rw [readyDomain];exact memoryDomain) (by rw [readyMemory];exact memoryAt) (by rw [readyDomain];exact pcDomain) (by rw [readyMemory];exact pcAt) (by rw [readyGlobals];exact atCurrent) (by intro offset member;rw [readyDomain];exact headerDomain offset member) (by rw [readyMemory];exact baseAt) (by rw [readyMemory];exact indexAt) (by rw [readyMemory];exact capacityAt) positive capacityBound indexBound bufferExtent (by rw [readyGlobals];exact atScratch) (by rw [readyGlobals];exact atFrontier) ordered scratchBeforeFrame frameExtent (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 exact ⟨zero,funding.after_memory (by rw [scope]) (by rw [scope])⟩
#print axioms mload_saturated_tail_returned_funding
end InitECandidate.Runtime

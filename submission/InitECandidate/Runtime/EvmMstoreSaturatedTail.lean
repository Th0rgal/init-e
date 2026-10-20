import InitECandidate.Runtime.EvmMstorePcTail
import InitECandidate.Runtime.EvmMstoreWriteFrame
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Original MSTORE saturation, 32-byte writer, pc_add and return preserve actual
funding when the preceding charged call has supplied the concrete32-byte span. -/
theorem mstore_saturated_tail_returned_funding {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base scratch pc sa sb sc sd a b c d : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (domain : ∀offset∈([0,24] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base)
 (pcAt : s.memory (current.address+0)=.word pc)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : base.toNat+(evmSatWord sa sb sc sd).toNat+32≤scratch.toNat)
 (ordered : scratch.toNat≤current.address.toNat)
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (mstoreAt 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_mstore_3] at run
 obtain ⟨body,output,tail,scope,memory,globals,installed,domains,endian⟩:=funding_sat_word_declaration_geometry s post (ofString "s") (.var .local (ofString "start")) (mstoreAt 4) sa sb sc sd value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt]) code run
 let ready:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord sa sb sc sd))) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mstoreAt 4)=_ at tail
 have readyMem : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domains
 have readyCode : ready.code=s.code:=installed
 have readyEndian : ready.be=s.be:=endian
 have layoutReady : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=layout.after_memory readyMem readyDomain
 obtain ⟨written,pcRun,funding,localsKept,globalsKept,domainKept,endianKept,codeKept,keptUpper⟩:=mstore_write_returned_frame ready output upper current ancestors layoutReady base (evmSatWord sa sb sc sd) scratch a b c d value (by rw [readyGlobals];exact atFrame) (by rw [readyDomain];exact domain 24 (by simp)) (by rw [readyMem];exact baseAt) (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using valueAt) extent ordered (readyCode.trans code) (by rw [readyDomain];exact domOK) tail
 have writtenPc : written.memory (current.address+0)=.word pc := by
  rw [keptUpper (current.address+0) (by simpa using ordered),readyMem]
  exact pcAt
 obtain ⟨zero,finalFunding,finalMem,finalGlobals,finalDomain,finalEndian,finalCode⟩:=mstore_pc_tail_returned_funding written output upper current ancestors funding pc value (by rw [globalsKept,readyGlobals];exact atFrame) (by rw [domainKept,readyDomain];exact domain 0 (by simp)) writtenPc (codeKept.trans (readyCode.trans code)) pcRun
 refine ⟨zero,?_,?_,?_,?_,?_⟩
 · exact finalFunding.after_memory (by rw [scope]) (by rw [scope])
 · rw [scope,finalGlobals,globalsKept,readyGlobals]
 · rw [scope,finalDomain,domainKept,readyDomain]
 · rw [scope,finalEndian,endianKept,readyEndian]
 · rw [scope,finalCode,codeKept,readyCode]
#print axioms mstore_saturated_tail_returned_funding
end InitECandidate.Runtime

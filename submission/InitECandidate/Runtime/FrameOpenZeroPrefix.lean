import InitECandidate.Runtime.FrameOpenSource
import InitECandidate.Runtime.MemzeroNormalZeroCells
import InitECandidate.Runtime.ScratchDeclarationReturnedContract
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure FrameOpenZeroReady {F : Type} (original ready : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) : Prop where
 atRecord : ready.locals.lookup (ofString "rec")=some (.val (.word (scratchAllocationEnd scratch 104)))
 otherLocals : ∀key,key≠ofString "rec" → ready.locals.lookup key=original.locals.lookup key
 globals : ready.globals=original.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd scratch 104)))
 domain : ready.memaddrs=original.memaddrs
 endian : ready.be=original.be
 code : ready.code=original.code
 lower : frame.toNat≤(scratchAllocationEnd scratch 104).toNat
 extent : (scratchAllocationEnd scratch 104).toNat+104≤scratch.toNat
 zeroWords : ∀offset : Nat,offset+8≤104 → offset%8=0 → 
  ready.memory (scratchAllocationEnd scratch 104+BitVec.ofNat 64 offset)=.word 0
 upperMemory : ∀watched : BitVec 64,scratch.toNat≤watched.toNat → ready.memory watched=original.memory watched

/-- Actual record allocation and original memzero prefix of frame_open. All
13 continuation record words are zero after the same successful returned path, regardless
of its actual fuel. Only its real aligned workspace domain is assumed. -/
theorem frame_open_zero_prefix_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame : BitVec 64) (value : ValueHOL 64)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (domain : ∀offset : Nat,offset<104 → s.memaddrs
  (panByteAlignHOL (scratchAllocationEnd scratch 104+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (frameOpenAt 2)=(some (.returned value),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (frameOpenAt 4)=(some (.returned value),output) ∧
 FrameOpenZeroReady s ready scratch frame ∧
 post.memory=output.memory ∧post.globals=output.globals ∧post.memaddrs=output.memaddrs ∧post.be=output.be ∧post.code=output.code := by
 classical
 rw [source_frame_open_2] at run
 obtain ⟨allocationPost,output,tailRun,postEq,memory,allocatedDomain,allocatedEndian,installed,globals,lower,extent⟩:=
  scratch_declaration_returned_contract s post (ofString "rec") (.const 104) (frameOpenAt 3) scratch 104 frame value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) scratchGlobal frameGlobal ordered code run
 let record:=scratchAllocationEnd scratch 104
 change record.toNat+104≤scratch.toNat at extent
 let beforeZero:=setVarHOLFinite (ofString "rec") (.val (.word record)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState beforeZero (frameOpenAt 3)=_ at tailRun
 have atRecord : beforeZero.locals.lookup (ofString "rec")=some (.val (.word record)) := by
  simp [beforeZero,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_frame_open_3] at tailRun
 obtain ⟨ready,zeroRun,nextRun⟩:=encode_header_seq_returned_of_no_return beforeZero output _ _ value
  (fun v=>(evaluate_handlerFree_call_control beforeZero _ _ _).2.2 v) tailRun
 have zeroArgs : evalListHOLFinite beforeZero (h:=fun a=>Classical.propDecidable (beforeZero.memaddrs a))
  [.var .local (ofString "rec"),.const 104]=some [.val (.word record),.val (.word (104#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atRecord]
 have aligned : record.toNat%8=0:=scratchAllocationEnd_mask_aligned scratch 104
 have small : record.toNat+(104#64).toNat≤33806089496:=by change record.toNat+104≤33806089496;omega
 have zeroDomain : ∀offset : Nat,offset<(104#64).toNat → beforeZero.memaddrs (panByteAlignHOL (record+BitVec.ofNat 64 offset)) := by
  intro offset inside
  change allocationPost.memaddrs _
  rw [allocatedDomain]
  exact domain offset inside
 have zero:=memzero_aligned_normal_zero_cells beforeZero ready _ _ record 104 zeroArgs (installed.trans code) small aligned zeroDomain zeroRun
 have globalFrame:=(memzero_call_globals_frame [.var .local (ofString "rec"),.const 104]) beforeZero (installed.trans code)
 have metadata:=evaluateHOLFiniteState_metadata beforeZero (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "rec"),.const 104])
 rw [zeroRun] at globalFrame metadata
 have outside : record.toNat+(104#64).toNat≤scratch.toNat:=extent
 obtain ⟨unusedFrame,locals⟩:=memzero_call_normal_memory beforeZero ready _ record 104 scratch zeroArgs (installed.trans code) aligned small (Or.inr outside) zeroRun
 have context : FrameOpenZeroReady s ready scratch frame := by
  constructor
  · rw [locals];exact atRecord
  · intro key different
    rw [locals]
    simpa [beforeZero,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using (rfl : s.locals.lookup key=s.locals.lookup key)
  · exact globalFrame.trans globals
  · exact metadata.2.1.trans allocatedDomain
  · exact metadata.2.2.1.trans allocatedEndian
  · exact metadata.1.trans installed
  · exact lower
  · exact extent
  · intro offset within offsetAligned
    apply ZeroBytePrefix.word ready record 104 offset zero within (by omega)
    omega
  · intro watched above
    have frameWord:=memzero_call_normal_memory beforeZero ready _ record 104 watched zeroArgs (installed.trans code) aligned small
     (Or.inr (by change record.toNat+104≤watched.toNat;omega)) zeroRun
    exact frameWord.1.trans (congrFun memory watched)
 refine ⟨ready,output,nextRun,context,?_,?_,?_,?_,?_⟩
 all_goals rw [postEq]
#print axioms frame_open_zero_prefix_returned
end InitECandidate.Runtime

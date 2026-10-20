import InitECandidate.Runtime.FrameNewSource
import InitECandidate.Runtime.FrameMemoryDeclarationReturnedContract
import InitECandidate.Runtime.ReturnedWordStorePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure FrameNewMemoryReady {F : Type} (original ready : PanSemStateFiniteExact 64 F) (record frame scratch mark : BitVec 64) : Prop where
 atMemory : ready.locals.lookup (ofString "mem")=some (.val (.word frame))
 otherLocals : ∀key,key≠ofString "mem" → ready.locals.lookup key=original.locals.lookup key
 globals : ready.globals=original.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd frame 1024)))
 memory : ready.memory=storePlanMemory original.memory [(record+224,mark),(record+24,frame),(record+40,1024)]
 domain : ready.memaddrs=original.memaddrs
 endian : ready.be=original.be
 code : ready.code=original.code
 coverage : frame.toNat+1024≤(allocationEnd frame 1024).toNat
 upper : (allocationEnd frame 1024).toNat≤scratch.toNat
 aligned : (allocationEnd frame 1024).toNat%8=0

/-- Actual upward EVM-memory allocation and real three frame_new stores.
The returned body itself supplies the space checks and every successful store. -/
theorem frame_new_memory_prefix_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record frame scratch mark : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMark : s.locals.lookup (ofString "mem_mark")=some (.val (.word mark)))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (frameNewAt 8)=(some (.returned value),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (frameNewAt 12)=(some (.returned value),output) ∧
 FrameNewMemoryReady s ready record frame scratch mark ∧
 post.memory=output.memory ∧post.globals=output.globals ∧post.memaddrs=output.memaddrs ∧post.be=output.be ∧post.code=output.code := by
 rw [source_frame_new_8] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const 1024]=
  some [.val (.word (1024#64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
 obtain ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,installed,globals,coverage,upper,aligned⟩:=
  frame_memory_declaration_returned_contract s post (ofString "mem") _ (frameNewAt 9) frame 1024 scratch value args frameGlobal scratchGlobal ordered cap code run
 let beforeStores:=setVarHOLFinite (ofString "mem") (.val (.word frame)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState beforeStores (frameNewAt 9)=_ at tailRun
 have recordLocal : beforeStores.locals.lookup (ofString "e")=some (.val (.word record)) := by
  simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
 have markLocal : beforeStores.locals.lookup (ofString "mem_mark")=some (.val (.word mark)) := by
  simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atMark
 have memoryLocal : beforeStores.locals.lookup (ofString "mem")=some (.val (.word frame)) := by
  simp [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 let plan : List (BitVec 64×BitVec 64):=[(record+224,mark),(record+24,frame),(record+40,1024)]
 have supported : BoundReturnedStorePrefix (F:=F) beforeStores.locals (frameNewAt 9) (frameNewAt 12) plan := by
  rw [source_frame_new_9]
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using markLocal
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using memoryLocal
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simp [evalHOLExact]
  exact .finish _
 let ready:={beforeStores with memory:=storePlanMemory beforeStores.memory plan}
 have nextRun:=evaluate_bound_returned_store_prefix supported beforeStores output value rfl tailRun
 have context : FrameNewMemoryReady s ready record frame scratch mark := by
  constructor
  · exact memoryLocal
  · intro key different
    simpa [ready,beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using (rfl : s.locals.lookup key=s.locals.lookup key)
  · exact globals
  · change storePlanMemory allocationPost.memory plan=_
    rw [memory]
  · exact domain
  · exact endian
  · exact installed
  · exact coverage
  · exact upper
  · exact aligned
 refine ⟨ready,output,nextRun,context,?_,?_,?_,?_,?_⟩
 all_goals rw [postEq]
#print axioms frame_new_memory_prefix_returned
end InitECandidate.Runtime

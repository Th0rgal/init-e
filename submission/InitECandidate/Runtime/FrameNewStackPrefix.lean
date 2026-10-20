import InitECandidate.Runtime.FrameNewSource
import InitECandidate.Runtime.ScratchDeclarationReturnedContract
import InitECandidate.Runtime.ReturnedWordStorePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure FrameNewStackReady {F : Type} (original ready : PanSemStateFiniteExact 64 F) (record frame mark : BitVec 64) : Prop where
 atStack : ready.locals.lookup (ofString "stk")=some (.val (.word (scratchAllocationEnd record 1024)))
 otherLocals : ∀key,key≠ofString "stk" → ready.locals.lookup key=original.locals.lookup key
 globals : ready.globals=original.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd record 1024)))
 memory : ready.memory=storePlanMemory original.memory [(record+208,mark),(record+8,scratchAllocationEnd record 1024),(record+232,32)]
 domain : ready.memaddrs=original.memaddrs
 endian : ready.be=original.be
 code : ready.code=original.code
 lower : frame.toNat≤(scratchAllocationEnd record 1024).toNat
 extent : (scratchAllocationEnd record 1024).toNat+1024≤record.toNat

/-- Actual frame_new stack allocation and three following record stores.
Both scratch guards and each store success follow from this returned run. -/
theorem frame_new_stack_prefix_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record frame mark : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMark : s.locals.lookup (ofString "stack_mark")=some (.val (.word mark)))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word record)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤record) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (frameNewAt 4)=(some (.returned value),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (frameNewAt 8)=(some (.returned value),output) ∧
 FrameNewStackReady s ready record frame mark ∧
 post.memory=output.memory ∧post.globals=output.globals ∧post.memaddrs=output.memaddrs ∧post.be=output.be ∧post.code=output.code := by
 rw [source_frame_new_4] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.panop .mul [.const 32,.const 32]]=
  some [.val (.word (1024#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord]
 obtain ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,installed,globals,lower,extent⟩:=
  scratch_declaration_returned_contract s post (ofString "stk") _ (frameNewAt 5) record 1024 frame value args scratchGlobal frameGlobal ordered code run
 let stack:=scratchAllocationEnd record 1024
 let beforeStores:=setVarHOLFinite (ofString "stk") (.val (.word stack)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState beforeStores (frameNewAt 5)=_ at tailRun
 have recordLocal : beforeStores.locals.lookup (ofString "e")=some (.val (.word record)) := by
  simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
 have markLocal : beforeStores.locals.lookup (ofString "stack_mark")=some (.val (.word mark)) := by
  simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atMark
 have stackLocal : beforeStores.locals.lookup (ofString "stk")=some (.val (.word stack)) := by
  simp [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 let plan : List (BitVec 64×BitVec 64):=[(record+208,mark),(record+8,stack),(record+232,32)]
 have supported : BoundReturnedStorePrefix (F:=F) beforeStores.locals (frameNewAt 5) (frameNewAt 8) plan := by
  rw [source_frame_new_5]
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using markLocal
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using stackLocal
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,locals,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simp [evalHOLExact]
  exact .finish _
 let ready:={beforeStores with memory:=storePlanMemory beforeStores.memory plan}
 have nextRun:=evaluate_bound_returned_store_prefix supported beforeStores output value rfl tailRun
 have context : FrameNewStackReady s ready record frame mark := by
  constructor
  · exact stackLocal
  · intro key different
    simpa [ready,beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using (rfl : s.locals.lookup key=s.locals.lookup key)
  · exact globals
  · change storePlanMemory allocationPost.memory plan=_
    rw [memory]
  · exact domain
  · exact endian
  · exact installed
  · exact lower
  · exact extent
 refine ⟨ready,output,nextRun,context,?_,?_,?_,?_,?_⟩
 all_goals rw [postEq]
#print axioms frame_new_stack_prefix_returned
end InitECandidate.Runtime

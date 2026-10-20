import InitECandidate.Runtime.ScratchHashTailReturnedFrame
import InitECandidate.Runtime.ScratchListReturnedFrame
import InitECandidate.Runtime.FundingAllocationReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

/-- Complete actual fixed scratch hash constructor used by frame_new. Six
real allocations descend below the entry frontier; every original header
store and the actual occupancy zeroing are included in the memory frame.
No successful-room, accessible-memory, fuel, or callee-frame callback. -/
theorem scratch_hash_20_4_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame watched : BitVec 64) (value : ValueHOL 64)
 (atKey : s.locals.lookup (ofString "key_len")=some (.val (.word (20#64))))
 (atCap : s.locals.lookup (ofString "cap")=some (.val (.word (4#64))))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_new_scratch)=(some (.returned value),post)) :
 ∃table keys vals used order orderPos : BitVec 64,value=.val (.word table) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word orderPos)) ∧
 frame.toNat≤orderPos.toNat ∧orderPos.toNat+32≤order.toNat ∧order.toNat+32≤used.toNat ∧
 used.toNat+4≤vals.toNat ∧vals.toNat+32≤keys.toNat ∧keys.toNat+96≤table.toNat ∧
 table.toNat+72≤scratch.toNat ∧post.memory watched=s.memory watched := by
 classical
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (scratchHashAt 0)=_ at run
 rw [source_scratch_hash_0] at run
 obtain ⟨allocationPost,outer,tableRun,tablePost,memory,domain,endian,installed,globals,lower,extent⟩:=
  scratch_declaration_returned_contract s post (ofString "t") (.const 72) (scratchHashAt 1) scratch 72 frame value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) scratchGlobal frameGlobal ordered code run
 let table:=scratchAllocationEnd scratch 72
 change frame.toNat≤table.toNat at lower
 change table.toNat+72≤scratch.toNat at extent
 let ready:=setVarHOLFinite (ofString "t") (.val (.word table)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState ready (scratchHashAt 1)=_ at tableRun
 have atTable : ready.locals.lookup (ofString "t")=some (.val (.word table)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have keyReady : ready.locals.lookup (ofString "key_len")=some (.val (.word (20#64))) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKey
 have capReady : ready.locals.lookup (ofString "cap")=some (.val (.word (4#64))) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCap
 rw [source_scratch_hash_1] at tableRun
 obtain ⟨strideValue,output,strideEval,prefixRun,stridePost⟩:=funding_declaration_returned_context tableRun
 have strideEq : strideValue=.val (.word (24#64)) := by
  have folded : AndOp.and (27#64) (AndOp.and (18446744073709551608#64) (18446744073709551615#64))=(24#64) := by decide
  simpa [scratchHashStrideExpression,evalHOLExact,evalListHOLExact,keyReady,wordOpHOL,wordOp,valueIsWord,valueWord,folded] using strideEval.symm
 subst strideValue
 let beforeStores:=setVarHOLFinite (ofString "stride") (.val (.word (24#64))) ready
 change evaluateHOLFiniteState beforeStores (scratchHashAt 2)=_ at prefixRun
 have context : ScratchHashBuilderContext beforeStores table frame table := by
  constructor
  · simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTable
  · simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using capReady
  · simp [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [beforeStores,ready,setVarHOLFinite,globals,HolFiniteMapExact.lookup_update,FUPDATE,table]
  · simpa (config:={decide:=true}) [beforeStores,ready,setVarHOLFinite,globals,HolFiniteMapExact.lookup_update,FUPDATE] using frameGlobal
  · exact BitVec.le_def.mpr lower
  · exact installed.trans code
 have keyBefore : beforeStores.locals.lookup (ofString "key_len")=some (.val (.word (20#64))) := by
  simpa (config:={decide:=true}) [beforeStores,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using keyReady
 let plan : List (BitVec 64×BitVec 64):=[(table+0,20),(table+8,24),(table+16,4),(table+24,0)]
 have supported : BoundReturnedStorePrefix (F:=F) beforeStores.locals (scratchHashAt 2) (scratchHashAt 6) plan := by
  rw [source_scratch_hash_2]
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [scratchHashAddress,evalHOLExact,evalListHOLExact,locals,context.atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using keyBefore
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [scratchHashAddress,evalHOLExact,evalListHOLExact,locals,context.atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using context.atStride
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [scratchHashAddress,evalHOLExact,evalListHOLExact,locals,context.atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using context.atCap
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [scratchHashAddress,evalHOLExact,evalListHOLExact,locals,context.atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simp [evalHOLExact]
  exact .finish _
 let afterStores:={beforeStores with memory:=storePlanMemory beforeStores.memory plan}
 have tailRun:=evaluate_bound_returned_store_prefix supported beforeStores output value rfl prefixRun
 have tailContext:=context.with_memory (storePlanMemory beforeStores.memory plan)
 change ScratchHashBuilderContext afterStores table frame table at tailContext
 have tailCap : table.toNat≤33806089496:=by omega
 have tailAbove : table.toNat≤watched.toNat:=by omega
 have separated : ∀offset∈([32,40,48,56,64] : List (BitVec 64)),watched≠table+offset := by
  intro offset member
  apply scratch_record_cell_below_frontier table offset watched 72 scratch.toNat extent _ (by omega) above
  simp at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;>decide
 obtain ⟨keys,vals,used,order,orderPos,valueEq,tailGlobals,frameBound,orderPosBound,orderBound,usedBound,valsBound,keysBound,tailFrame⟩:=
  scratch_hash_tail_20_4_returned_frame afterStores output table frame table watched value tailContext tailCap tailAbove separated tailRun
 refine ⟨table,keys,vals,used,order,orderPos,valueEq,?_,frameBound,orderPosBound,orderBound,usedBound,valsBound,keysBound,extent,?_⟩
 · rw [tablePost,stridePost]
   change output.globals=_
   rw [tailGlobals]
   change allocationPost.globals.update _=_
   rw [globals]
   apply HolFiniteMapExact.ext
   funext key
   by_cases same : ofString "scratch_ptr"=key <;>simp [HolFiniteMapExact.lookup_update,FUPDATE,same]
 · rw [tablePost,stridePost]
   change output.memory watched=_
   rw [tailFrame]
   change storePlanMemory allocationPost.memory plan watched=_
   rw [memory]
   have separatedHead : ∀offset∈([0,8,16,24] : List (BitVec 64)),watched≠table+offset := by
    intro offset member
    apply scratch_record_cell_below_frontier table offset watched 72 scratch.toNat extent _ (by omega) above
    simp at member
    rcases member with rfl|rfl|rfl|rfl <;>decide
   have a:=separatedHead 0 (by simp)
   have b:=separatedHead 8 (by simp)
   have c:=separatedHead 16 (by simp)
   have d:=separatedHead 24 (by simp)
   change watched≠table+8#64 at b
   change watched≠table+16#64 at c
   change watched≠table+24#64 at d
   have aZero : watched≠table:=by simpa using a
   simp [plan,storePlanMemory,aZero,b,c,d]
#print axioms scratch_hash_20_4_returned_frame
end InitECandidate.Runtime

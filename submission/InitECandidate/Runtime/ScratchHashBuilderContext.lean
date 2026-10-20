import InitECandidate.Runtime.ScratchDeclarationReturnedContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Concrete locals/workspace needed by the fixed original hash constructor. -/
structure ScratchHashBuilderContext {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table frame pointer : BitVec 64) : Prop where
 atTable : s.locals.lookup (ofString "t")=some (.val (.word table))
 atCap : s.locals.lookup (ofString "cap")=some (.val (.word (4#64)))
 atStride : s.locals.lookup (ofString "stride")=some (.val (.word (24#64)))
 scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer))
 frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame))
 ordered : frame≤pointer
 code : s.code=originalRuntimeCode

/-- Replacing only memory leaves the concrete builder locals/workspace intact. -/
theorem ScratchHashBuilderContext.with_memory {F : Type} {s : PanSemStateFiniteExact 64 F}
 {table frame pointer : BitVec 64} (valid : ScratchHashBuilderContext s table frame pointer)
 (memory : BitVec 64→HolWordLab 64) : ScratchHashBuilderContext {s with memory:=memory} table frame pointer :=
 ⟨valid.atTable,valid.atCap,valid.atStride,valid.scratchGlobal,valid.frameGlobal,valid.ordered,valid.code⟩

/-- A real returned scratch declaration produces the next concrete builder
state, with the exact rounded pointer and footprint derived from its guards. -/
theorem ScratchHashBuilderContext.allocate_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
 {table frame pointer : BitVec 64} (valid : ScratchHashBuilderContext s table frame pointer)
 (post : PanSemStateFiniteExact 64 F) (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64)
 (size : BitVec 64) (value : ValueHOL 64)
 (notTable : name≠ofString "t") (notCap : name≠ofString "cap") (notStride : name≠ofString "stride")
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [argument] tail)=(some (.returned value),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 ScratchHashBuilderContext ready table frame (scratchAllocationEnd pointer size) ∧
 ready.locals.lookup name=some (.val (.word (scratchAllocationEnd pointer size))) ∧
 ready.memory=s.memory ∧ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧
 ready.globals=s.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd pointer size))) ∧
 (scratchAllocationEnd pointer size).toNat+size.toNat≤pointer.toNat := by
 obtain ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,code,globals,lower,extent⟩:=
  scratch_declaration_returned_contract s post name argument tail pointer size frame value args
   valid.scratchGlobal valid.frameGlobal valid.ordered valid.code run
 let ready:=setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) {allocationPost with locals:=s.locals}
 have context : ScratchHashBuilderContext ready table frame (scratchAllocationEnd pointer size) := by
  constructor
  · simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notTable] using valid.atTable
  · simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notCap] using valid.atCap
  · simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notStride] using valid.atStride
  · simp [ready,setVarHOLFinite,globals,HolFiniteMapExact.lookup_update,FUPDATE]
  · have different : ofString "scratch_ptr"≠ofString "frame_mem_ptr" := by decide
    simpa [ready,setVarHOLFinite,globals,HolFiniteMapExact.lookup_update,FUPDATE,different] using valid.frameGlobal
  · exact BitVec.le_def.mpr lower
  · exact code.trans valid.code
 refine ⟨ready,output,tailRun,postEq,context,?_,memory,domain,endian,globals,extent⟩
 simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms ScratchHashBuilderContext.with_memory
#print axioms ScratchHashBuilderContext.allocate_returned
end InitECandidate.Runtime

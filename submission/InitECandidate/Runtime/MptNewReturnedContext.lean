import InitECandidate.Runtime.MptNewRuntimeBound
import InitECandidate.Runtime.HeapDeclarationReturnedContract
import InitECandidate.Runtime.ReturnedWordStorePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptNewReturn : ProgHOL 64:=.return (.var .local (ofString "m"))
def mptNewTail : ProgHOL 64:=
 .seq (.store (.op .add [.var .local (ofString "m"),.const 0]) (.var .local (ofString "root_node")))
  (.seq (.store (.op .add [.var .local (ofString "m"),.const 8]) (.var .local (ofString "secured"))) mptNewReturn)
theorem source_mpt_new_constructor : sourceFunctionBody Guest.guestFn_mpt_new=
 .decCall (ofString "m") .one (ofString "alloc") [.const 16] mptNewTail := by
 rw [sourceFunctionBody_eq_structural]
 rfl

/-- Actual returned mpt_new supplies both initialized header words, the
allocation extent and the old-memory frame at any fuel. Allocation/store
success is derived from this original returned run, with no reserve premise. -/
theorem mpt_new_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer root secured : BitVec 64) (value : ValueHOL 64)
 (atRoot : s.locals.lookup (ofString "root_node")=some (.val (.word root)))
 (atSecured : s.locals.lookup (ofString "secured")=some (.val (.word secured)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mpt_new)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧post.memory pointer=.word root ∧post.memory (pointer+8)=.word secured ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 16))) ∧
 pointer.toNat+16≤(allocationEnd pointer 16).toNat ∧(allocationEnd pointer 16).toNat%8=0 ∧
 (allocationEnd pointer 16).toNat≤33806089496 ∧
 (∀watched : BitVec 64,watched.toNat<pointer.toNat→post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have originalRun:=run
 rw [source_mpt_new_constructor] at run
 obtain ⟨allocated,output,tailRun,postEq,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "m") (.const 16) mptNewTail pointer 16 value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) atHeap code run
 let ready:=setVarHOLFinite (ofString "m") (.val (.word pointer)) {allocated with locals:=s.locals}
 have atM : ready.locals.lookup (ofString "m")=some (.val (.word pointer)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have rootLocal : ready.locals.lookup (ofString "root_node")=some (.val (.word root)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRoot
 have securedLocal : ready.locals.lookup (ofString "secured")=some (.val (.word secured)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSecured
 let plan : List (BitVec 64×BitVec 64):=[(pointer,root),(pointer+8,secured)]
 have supported : BoundReturnedStorePrefix (F:=F) ready.locals mptNewTail mptNewReturn plan := by
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [evalHOLExact,evalListHOLExact,locals,atM,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using rootLocal
  apply BoundReturnedStorePrefix.store
  · intro state locals
    simp [evalHOLExact,evalListHOLExact,locals,atM,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using securedLocal
  exact .finish _
 have returnRun:=evaluate_bound_returned_store_prefix supported ready output value rfl tailRun
 let finalState:={ready with memory:=storePlanMemory ready.memory plan}
 have exactReturn : evaluateHOLFiniteState finalState mptNewReturn=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite finalState) := by
  simp [mptNewReturn,evaluateHOLFiniteState_return,evalHOLExact,show finalState.locals.lookup (ofString "m")=some (.val (.word pointer)) from atM,shapeOfHOLExact]
 have equal:=Prod.mk.inj (returnRun.symm.trans exactReturn)
 have returned : value=.val (.word pointer):=PanSemResultExact.returned.inj (Option.some.inj equal.1)
 have endpoint : output=emptyLocalsHOLFinite finalState:=equal.2
 have sumBound:=allocationGuard_sum_bound pointer 16 capped request
 have coverage:=allocationEnd_covers pointer 16 sumBound
 have extent : pointer.toNat+16≤33806089496 := by change pointer.toNat+16≤33806089496 at sumBound;exact sumBound
 have metadata:=evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_mpt_new)
 rw [originalRun] at metadata
 refine ⟨returned,?_,?_,?_,coverage.1,coverage.2.2,finish,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [postEq,endpoint]
   simp [finalState,plan,storePlanMemory,List.foldl,emptyLocalsHOLFinite]
 · rw [postEq,endpoint]
   simp [finalState,plan,storePlanMemory,List.foldl,emptyLocalsHOLFinite]
 · rw [postEq,endpoint]
   exact globals
 · intro watched before
   rw [postEq,endpoint]
   have different : watched≠pointer:=by intro equal;subst equal;omega
   have natural : (pointer+8#64).toNat=pointer.toNat+8:=BitVec.toNat_add_of_lt (by change pointer.toNat+8<2^64;omega)
   have different8 : watched≠pointer+8#64:=by intro equal;subst equal;omega
   simpa [finalState,plan,storePlanMemory,List.foldl,different,different8,emptyLocalsHOLFinite,ready,setVarHOLFinite] using congrFun memory watched
#print axioms source_mpt_new_constructor
#print axioms mpt_new_returned_context
end InitECandidate.Runtime

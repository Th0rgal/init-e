import InitECandidate.Runtime.ScratchDeclarationReturnedContract
import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.ReturnedStorePlanMemory
import InitECandidate.Runtime.FundingReturnedLocal
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def scratchListAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_lst_new_scratch)
def scratchListAddress (offset : BitVec 64) : ExpHOL 64 :=
 .op .add [.var .local (ofString "l"),.const offset]
theorem source_scratch_list_initial : scratchListAt 0=
 .decCall (ofString "l") .one (ofString "scratch_alloc") [.const 24] (scratchListAt 1) := rfl
theorem source_scratch_list_data : scratchListAt 1=
 .decCall (ofString "p") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "esz"),.var .local (ofString "cap")]] (scratchListAt 2) := rfl
theorem source_scratch_list_stores : scratchListAt 2=
 .seq (.store (scratchListAddress 0) (.var .local (ofString "p")))
  (.seq (.store (scratchListAddress 8) (.const 0))
   (.seq (.store (scratchListAddress 16) (.var .local (ofString "cap"))) (.return (.var .local (ofString "l"))))) := rfl

theorem scratch_record_cell_below_frontier (record offset watched : BitVec 64) (size frontier : Nat)
 (extent : record.toNat+size≤frontier) (inside : offset.toNat<size) (cap : frontier≤2^64)
 (above : frontier≤watched.toNat) : watched≠record+offset := by
 intro equal
 have bounded : record.toNat+offset.toNat<2^64 := by omega
 have eq:=congrArg BitVec.toNat equal
 rw [BitVec.toNat_add_of_lt bounded] at eq
 omega

/-- The original fixed frame-log constructor (8-byte elements, capacity 4)
returns a real zero-count list and frames all words above its entry scratch
frontier. Both allocations and all three stores come from the actual run. -/
theorem scratch_list_8_4_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame watched : BitVec 64) (value : ValueHOL 64)
 (atEsz : s.locals.lookup (ofString "esz")=some (.val (.word 8)))
 (atCap : s.locals.lookup (ofString "cap")=some (.val (.word 4)))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_lst_new_scratch)=(some (.returned value),post)) :
 ∃list data : BitVec 64,value=.val (.word list) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word data)) ∧
 frame.toNat≤data.toNat ∧data.toNat+32≤list.toNat ∧list.toNat+24≤scratch.toNat ∧
 post.memory watched=s.memory watched ∧post.memory (list+0)=.word data ∧
 post.memory (list+8)=.word 0 ∧post.memory (list+16)=.word 4 := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (scratchListAt 0)=_ at run
 rw [source_scratch_list_initial] at run
 obtain ⟨one,outer,oneRun,outerPost,oneMemory,oneDomain,oneEndian,oneCode,oneGlobals,oneLower,oneExtent⟩:=
  scratch_declaration_returned_contract s post (ofString "l") (.const 24) (scratchListAt 1) scratch 24 frame value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) scratchGlobal frameGlobal ordered code run
 let list:=scratchAllocationEnd scratch 24
 change frame.toNat≤list.toNat at oneLower
 change list.toNat+24≤scratch.toNat at oneExtent
 let first:=setVarHOLFinite (ofString "l") (.val (.word list)) {one with locals:=s.locals}
 change evaluateHOLFiniteState first (scratchListAt 1)=_ at oneRun
 have firstScratch : first.globals.lookup (ofString "scratch_ptr")=some (.val (.word list)) := by
  simp [first,setVarHOLFinite,oneGlobals,HolFiniteMapExact.lookup_update,FUPDATE,list]
 have firstFrame : first.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,oneGlobals,HolFiniteMapExact.lookup_update,FUPDATE] using frameGlobal
 have atList : first.locals.lookup (ofString "l")=some (.val (.word list)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have eszFirst : first.locals.lookup (ofString "esz")=some (.val (.word 8)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atEsz
 have capFirst : first.locals.lookup (ofString "cap")=some (.val (.word 4)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCap
 have dataArgs : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a))
  [.panop .mul [.var .local (ofString "esz"),.var .local (ofString "cap")]]=some [.val (.word (32#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,eszFirst,capFirst,panOpHOL,valueIsWord,valueWord]
 rw [source_scratch_list_data] at oneRun
 obtain ⟨two,output,twoRun,innerPost,twoMemory,twoDomain,twoEndian,twoCode,twoGlobals,twoLower,twoExtent⟩:=
  scratch_declaration_returned_contract first outer (ofString "p") _ (scratchListAt 2) list 32 frame value dataArgs firstScratch firstFrame
   (BitVec.le_def.mpr oneLower) (oneCode.trans code) oneRun
 let data:=scratchAllocationEnd list 32
 change frame.toNat≤data.toNat at twoLower
 change data.toNat+32≤list.toNat at twoExtent
 let ready:=setVarHOLFinite (ofString "p") (.val (.word data)) {two with locals:=first.locals}
 change evaluateHOLFiniteState ready (scratchListAt 2)=_ at twoRun
 have lReady : ready.locals.lookup (ofString "l")=some (.val (.word list)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atList
 have pReady : ready.locals.lookup (ofString "p")=some (.val (.word data)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have capReady : ready.locals.lookup (ofString "cap")=some (.val (.word (4#64))) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using capFirst
 have plan : BoundReturnedStorePlan (F:=F) ready.locals (scratchListAt 2) [(list+0,data),(list+8,0),(list+16,4)] := by
  rw [source_scratch_list_stores]
  apply BoundReturnedStorePlan.store
  · intro state locals
    simp [scratchListAddress,evalHOLExact,evalListHOLExact,locals,lReady,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using pReady
  apply BoundReturnedStorePlan.store
  · intro state locals
    simp [scratchListAddress,evalHOLExact,evalListHOLExact,locals,lReady,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simp [evalHOLExact]
  apply BoundReturnedStorePlan.store
  · intro state locals
    simp [scratchListAddress,evalHOLExact,evalListHOLExact,locals,lReady,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro state locals
    simpa [evalHOLExact,locals] using capReady
  exact .finish _ rfl
 have postMemory:=evaluate_bound_returned_store_plan_memory plan ready output value rfl twoRun
 have valueEq:=funding_return_local (scratchListAt 2) (ofString "l") (by decide_cbv) ready output (.val (.word list)) value lReady twoRun
 have globalsFrame : OriginalGlobalsFrame (scratchListAt 2):=originalGlobalsFrame_leaf _ (by intro watched;rfl)
 have globals:=globalsFrame ready (twoCode.trans (oneCode.trans code))
 rw [twoRun] at globals
 have cellSeparation : ∀offset∈([0,8,16] : List (BitVec 64)),watched≠list+offset := by
  intro offset member
  apply scratch_record_cell_below_frontier list offset watched 24 scratch.toNat oneExtent _ (by omega) above
  simp at member
  rcases member with rfl|rfl|rfl <;>decide
 have wholeMemory : post.memory=storePlanMemory s.memory [(list+0,data),(list+8,0),(list+16,4)] := by
  rw [outerPost,innerPost]
  change output.memory=_
  rw [postMemory]
  change storePlanMemory two.memory _=_
  rw [twoMemory]
  change storePlanMemory one.memory _=_
  rw [oneMemory]
 refine ⟨list,data,valueEq,?_,twoLower,twoExtent,oneExtent,?_,?_,?_,?_⟩
 · rw [outerPost,innerPost]
   change output.globals=_
   rw [globals]
   change two.globals=_
   rw [twoGlobals]
   change first.globals.update _=_
   rw [show first.globals=one.globals from rfl,oneGlobals]
   apply HolFiniteMapExact.ext
   funext key
   by_cases same : ofString "scratch_ptr"=key <;>simp [HolFiniteMapExact.lookup_update,FUPDATE,same,data]
 · rw [wholeMemory]
   have a:=cellSeparation 0 (by simp)
   have b:=cellSeparation 8 (by simp)
   have c:=cellSeparation 16 (by simp)
   change watched≠list+0#64 at a
   change watched≠list+8#64 at b
   change watched≠list+16#64 at c
   have aZero : watched≠list := by simpa using a
   simp [storePlanMemory,aZero,b,c]
 · rw [wholeMemory]
   simp [storePlanMemory]
 · rw [wholeMemory]
   simp [storePlanMemory]
 · rw [wholeMemory]
   simp [storePlanMemory]
#print axioms source_scratch_list_initial
#print axioms source_scratch_list_data
#print axioms source_scratch_list_stores
#print axioms scratch_record_cell_below_frontier
#print axioms scratch_list_8_4_returned_frame
end InitECandidate.Runtime

import InitECandidate.Runtime.WitnessUnwindNormalPrefix
import InitECandidate.Runtime.WitnessExtensionNormalHeapFrame
import InitECandidate.Runtime.WitnessExtensionWorkspaceFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_extension_nonempty_heap_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash heap : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496)
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindNonempty=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
    heap.toNat≤(allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat≤33806089496 ∧
    (allocationEnd heap 56).toNat%8=0 ∧
    post.globals.lookup (ofString "scratch_ptr")=s.globals.lookup (ofString "scratch_ptr") ∧
    post.globals.lookup (ofString "frame_mem_ptr")=s.globals.lookup (ofString "frame_mem_ptr") ∧
    ∀ watched : BitVec 64, watched.toNat<heap.toNat → result=0 ∨ watched≠result+24 →
      post.memory watched=s.memory watched := by
  obtain ⟨next,output,tailRun,locals,globals,codeEq,domain,endian,clock,memory,postMemory,postGlobals,postLocals⟩ :=
    witness_unwind_nonempty_normal_prefix s post top result hash atTop atResult hashReadable hashCell code run
  have other (name : MlS) (different : name ≠ ofString "hash") : next.locals.lookup name=s.locals.lookup name := by
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nextTop := (other _ (by decide)).trans atTop
  have stageNat : (top+8#64).toNat=top.toNat+8 := by
    rw [BitVec.toNat_add]
    change (top.toNat+8)%2^64=top.toNat+8
    exact Nat.mod_eq_of_lt (by omega)
  have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
    rw [BitVec.toNat_add]
    change (result.toNat+24)%2^64=result.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  have stageKept : next.memory (top+8#64)=s.memory (top+8#64) := by
    apply memory
    rcases resultAfterRecord with zero | lower
    · exact Or.inl zero
    · apply Or.inr
      intro same
      have equal := congrArg BitVec.toNat same
      rw [stageNat,resultNat] at equal
      omega
  have condition : @evalHOLExact 64 F _ next.toExact (fun a => Classical.propDecidable (next.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))=
      some (.val (.word (1#64))) := by
    simp [evalHOLExact,evalListHOLExact,nextTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,
      show next.memaddrs (top+8#64) from by rw [domain]; exact stageReadable,
      stageKept,stageCell,Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_ite,condition] at tailRun
  change evaluateHOLFiniteState next witnessUnwindExtension=(none,output) at tailRun
  obtain ⟨heapPost,mono,cap,aligned,frame⟩ := witness_extension_normal_heap_frame next output heap result
    ((other _ (by decide)).trans atResult) (by rw [globals]; exact atHeap)
    heapBound (codeEq.trans code) tailRun
  have workspace (name : MlS) (member : name∈witnessExtensionWorkspace) : output.globals.lookup name=s.globals.lookup name := by
    have kept := witness_extension_branch_workspace_frame next (codeEq.trans code) name member
    rw [tailRun] at kept
    exact kept.trans (by rw [globals])
  refine ⟨?_,mono,cap,aligned,?_,?_,?_⟩
  · rw [postGlobals]; exact heapPost
  · rw [postGlobals];exact workspace _ (by simp [witnessExtensionWorkspace])
  · rw [postGlobals];exact workspace _ (by simp [witnessExtensionWorkspace])
  · intro watched below separate
    exact (congrFun postMemory watched).trans ((frame watched below).trans (memory watched separate))

#print axioms witness_unwind_extension_nonempty_heap_frame
end InitECandidate.Runtime

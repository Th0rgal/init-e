import InitECandidate.Runtime.WitnessUnwindNormalPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_extension_nonempty_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash heap prev : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (prevCell : s.memory top=.word prev)
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (before : top.toNat<heap.toNat) (heapBound : heap.toNat≤33806089496)
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindNonempty=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode")=s.locals.lookup (ofString "mode") ∧ post.memory top=s.memory top := by
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
  have prevKept : next.memory top=s.memory top := by
    apply memory
    rcases resultAfterRecord with zero | lower
    · exact Or.inl zero
    · apply Or.inr
      intro same
      have equal := congrArg BitVec.toNat same
      rw [resultNat] at equal
      omega
  have facts := witness_extension_normal_progress next output top heap prev result nextTop
    ((other _ (by decide)).trans atResult) (prevKept.trans prevCell)
    (by rw [globals]; exact atHeap) before heapBound (codeEq.trans code) tailRun
  exact ⟨(postLocals _ (by decide)).trans facts.1,
    (postLocals _ (by decide)).trans facts.2.1,
    ((postLocals _ (by decide)).trans facts.2.2.1).trans (other _ (by decide)),
    (congrFun postMemory top).trans (facts.2.2.2.trans prevKept)⟩
#print axioms witness_unwind_extension_nonempty_normal_progress
end InitECandidate.Runtime

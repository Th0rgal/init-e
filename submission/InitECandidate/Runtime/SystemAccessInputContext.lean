import InitECandidate.Runtime.SystemMessageInputFields
import InitECandidate.Runtime.SystemAccessGasContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
structure SystemAccessInputContext {F : Type} (base mid : PanSemStateFiniteExact 64 F)
 (message target data dataSize codePointer codeSize : BitVec 64) : Prop
 extends SystemAccessGasContext base mid message where
 inputs : SystemMessageInputs mid message target data dataSize codePointer codeSize
variable {target data dataSize codePointer codeSize : BitVec 64}

theorem SystemAccessInputContext.after_table {F : Type} {base mid next : PanSemStateFiniteExact 64 F}
 {message pointer keyLength : BitVec 64} {name : MlS}
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (atHeap : mid.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (lower : message.toNat+176≤pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (different : ofString "m"≠name) (table : AccessTableReady mid name pointer keyLength next) :
 SystemAccessInputContext base next message target data dataSize codePointer codeSize :=
 ⟨ctx.toSystemAccessGasContext.after_table atHeap lower aligned capped different table,
  ctx.inputs.after_table lower capped table⟩
/-- A real accessed-set pointer store preserves the already initialized gas
word. Its domain follows from the concrete message extent, rather than a
successful-store premise. -/
theorem system_access_input_pointer_store_reaches {F : Type} (base mid : PanSemStateFiniteExact 64 F)
 (message pointer offset : BitVec 64) (name : MlS) (tail : ProgHOL 64)
 (ctx : SystemAccessInputContext base mid message target data dataSize codePointer codeSize)
 (atPointer : mid.locals.lookup name=some (.val (.word pointer)))
 (inside : offset.toNat<176) (different : offset≠40)
 (access : offset=152 ∨offset=160)
 (fullDomain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) :
 Reaches mid (.seq (.store (.op .add [.var .local (ofString "m"),.const offset]) (.var .local name)) tail)
  (fun next=>SystemAccessInputContext base next message target data dataSize codePointer codeSize) 0 tail := by
 obtain ⟨heap,atHeap,lower,aligned,capped⟩:=ctx.heap
 have natural : (message+offset).toNat=message.toNat+offset.toNat := BitVec.toNat_add_of_lt (by omega)
 have domain : mid.memaddrs (message+offset) := by
  rw [ctx.domain]
  exact fullDomain _ (by rw [natural];omega)
 have address : @evalHOLExact 64 F _ mid.toExact (fun a=>Classical.propDecidable (mid.memaddrs a))
  (.op .add [.var .local (ofString "m"),.const offset])=some (.val (.word (message+offset))) := by
  simp [evalHOLExact,evalListHOLExact,ctx.atMessage,wordOpHOL,wordOp,valueIsWord,valueWord]
 have value : @evalHOLExact 64 F _ mid.toExact (fun a=>Classical.propDecidable (mid.memaddrs a))
  (.var .local name)=some (.val (.word pointer)) := by simp [evalHOLExact,atPointer]
 have run:=evaluate_store_word mid (message+offset) pointer _ _ address value domain
 have distinct : (40#64 : BitVec 64)≠offset := Ne.symm different
 let next:=sourceWriteWord mid (message+offset) pointer
 have nextGas : next.memory (message+40)=.word 30000000 := by
  simpa [next,sourceWriteWord,distinct] using ctx.gas
 have ready : SystemAccessInputContext base next message target data dataSize codePointer codeSize:=
  ⟨⟨ctx.atMessage,ctx.code,ctx.domain,nextGas,ctx.globals,ctx.heap⟩,ctx.inputs.after_access_write pointer offset access⟩
 exact reaches_seq mid _ tail 0 (fun state=>SystemAccessInputContext base state message target data dataSize codePointer codeSize)
  (Or.inl ⟨next,ready,by simp [next,sourceWriteWord],by simp [next,sourceWriteWord],run⟩)

#print axioms SystemAccessInputContext.after_table
#print axioms system_access_input_pointer_store_reaches
end InitECandidate.Runtime

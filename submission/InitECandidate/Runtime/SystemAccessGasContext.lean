import InitECandidate.Runtime.AccessTableDeclarationReach
import InitECandidate.Runtime.SystemMessageGasSetup
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Concrete message gas and the live heap/locals needed between the two
actual system accessed-set constructors. -/
structure SystemAccessGasContext {F : Type} (base mid : PanSemStateFiniteExact 64 F) (message : BitVec 64) : Prop where
 atMessage : mid.locals.lookup (ofString "m")=some (.val (.word message))
 code : mid.code=originalRuntimeCode
 domain : mid.memaddrs=base.memaddrs
 gas : mid.memory (message+40)=.word 30000000
 globals : HeapGlobalsFrame base mid
 heap : ∃pointer : BitVec 64,mid.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)) ∧
  message.toNat+176≤pointer.toNat ∧pointer.toNat%8=0 ∧pointer.toNat≤33806089496

theorem SystemAccessGasContext.after_table {F : Type} {base mid next : PanSemStateFiniteExact 64 F}
 {message pointer keyLength : BitVec 64} {name : MlS}
 (ctx : SystemAccessGasContext base mid message)
 (atHeap : mid.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (lower : message.toNat+176≤pointer.toNat) (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (different : ofString "m"≠name) (table : AccessTableReady mid name pointer keyLength next) :
 SystemAccessGasContext base next message := by
 obtain ⟨atName,locals,code,domain,endian,memory,rel,rest⟩:=table
 have gasNat : (message+40#64).toNat=message.toNat+40 := BitVec.toNat_add_of_lt (by change message.toNat+40<2^64;omega)
 obtain ⟨newHeap,newAtHeap,mono,newAligned,newCapped⟩:=rel.2 pointer atHeap aligned capped
 refine ⟨(locals _ different).trans ctx.atMessage,code.trans ctx.code,domain.trans ctx.domain,
  (memory _ (by change (message+40#64).toNat<pointer.toNat;rw [gasNat];omega)).trans ctx.gas,?_,newHeap,newAtHeap,by omega,newAligned,newCapped⟩
 intro key ne
 exact (rel.1 key ne).trans (ctx.globals key ne)

/-- A real accessed-set pointer store preserves the already initialized gas
word. Its domain follows from the concrete message extent, rather than a
successful-store premise. -/
theorem system_access_pointer_store_reaches {F : Type} (base mid : PanSemStateFiniteExact 64 F)
 (message pointer offset : BitVec 64) (name : MlS) (tail : ProgHOL 64)
 (ctx : SystemAccessGasContext base mid message)
 (atPointer : mid.locals.lookup name=some (.val (.word pointer)))
 (inside : offset.toNat<176) (different : offset≠40)
 (fullDomain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a) :
 Reaches mid (.seq (.store (.op .add [.var .local (ofString "m"),.const offset]) (.var .local name)) tail)
  (fun next=>SystemAccessGasContext base next message) 0 tail := by
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
 have ready : SystemAccessGasContext base next message:=
  ⟨ctx.atMessage,ctx.code,ctx.domain,nextGas,ctx.globals,ctx.heap⟩
 exact reaches_seq mid _ tail 0 (fun state=>SystemAccessGasContext base state message)
  (Or.inl ⟨next,ready,by simp [next,sourceWriteWord],by simp [next,sourceWriteWord],run⟩)
#print axioms SystemAccessGasContext.after_table
#print axioms system_access_pointer_store_reaches
end InitECandidate.Runtime

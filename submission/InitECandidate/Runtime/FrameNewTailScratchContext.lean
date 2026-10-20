import InitECandidate.Runtime.FrameNewTailContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A real call to one of the three fixed original constructors transports
all concrete frame_new input/workspace facts and frames the old upper arena. -/
theorem FrameNewTailContext.scratch_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (kind : FrameNewScratchCallee) (post : PanSemStateFiniteExact 64 F) (name : MlS)
 (firstArgument secondArgument : ExpHOL 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (notRecord : name≠ofString "e") (notMessage : name≠ofString "msg")
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [firstArgument,secondArgument]=
  some [.val (.word kind.firstWord),.val (.word kind.secondWord)])
 (codeBound : kind.codeBound)
 (run : evaluateHOLFiniteState s (.decCall name .one kind.function [firstArgument,secondArgument] tail)=(some (.returned value),post)) :
 ∃pointer frontier : BitVec 64,∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 FrameNewTailContext ready record message codePointer codeLength accessAddresses accessSlots empty frame frontier ∧
 ready.locals.lookup name=some (.val (.word pointer)) ∧
 ready.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)) ∧
 frontier.toNat≤pointer.toNat ∧pointer.toNat≤scratch.toNat ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → ready.memory watched=s.memory watched) := by
 have cap : scratch.toNat≤33806089496:=by have:=valid.scratchBelow;have:=valid.recordBound;omega
 obtain ⟨pointer,frontier,bodyPost,output,tailRun,postEq,globals,lower,beforePointer,beforeScratch,wordFrame,domain,endian,code,memory⟩:=
  frame_new_scratch_declaration_returned kind s post name firstArgument secondArgument tail scratch frame scratch value args valid.atScratch valid.atFrame
   (BitVec.le_def.mpr valid.ordered) cap (Nat.le_refl _) valid.sourceCode codeBound run
 let ready:=setVarHOLFinite name (.val (.word pointer)) {bodyPost with locals:=s.locals}
 have atRecord : ready.locals.lookup (ofString "e")=some (.val (.word record)) := by
  simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notRecord] using valid.atRecord
 have atMessage : ready.locals.lookup (ofString "msg")=some (.val (.word message)) := by
  simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notMessage] using valid.atMessage
 have context:=valid.after_upper_frame ready frontier atRecord atMessage globals lower (beforePointer.trans beforeScratch) domain code memory
 refine ⟨pointer,frontier,ready,output,tailRun,postEq,context,?_,globals,beforePointer,beforeScratch,memory⟩
 simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem FrameNewTailContext.bitmap_arguments {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch) :
 evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
 [.load .one (frameNewLocalAddress (ofString "msg") 112),.load .one (frameNewLocalAddress (ofString "msg") 120)]=
 some [.val (.word codePointer),.val (.word codeLength)] := by
 have firstAddress:=eval_frame_new_local_address s (ofString "msg") message 112 valid.atMessage
 have secondAddress:=eval_frame_new_local_address s (ofString "msg") message 120 valid.atMessage
 have first : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (frameNewLocalAddress (ofString "msg") 112))=some (.val (.word codePointer)) := by
  rw [evalHOLExact,firstAddress]
  simp [isWfShapeExactHOL,memLoadHOLExact,toExact,valid.messageDomain 112 (by simp),valid.codeAt]
  exact ⟨valid.messageDomain 112 (by simp),valid.codeAt⟩
 have second : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (frameNewLocalAddress (ofString "msg") 120))=some (.val (.word codeLength)) := by
  rw [evalHOLExact,secondAddress]
  simp [isWfShapeExactHOL,memLoadHOLExact,toExact,valid.messageDomain 120 (by simp),valid.lengthAt]
  exact ⟨valid.messageDomain 120 (by simp),valid.lengthAt⟩
 simp only [evalListHOLFinite,evalListHOLExact,first,second]
#print axioms FrameNewTailContext.scratch_returned
#print axioms FrameNewTailContext.bitmap_arguments
end InitECandidate.Runtime

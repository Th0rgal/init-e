import InitECandidate.Runtime.FrameNewTailContext
import InitECandidate.Runtime.FrameNewCountCallFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem FrameNewTailContext.after_identity_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (post : PanSemStateFiniteExact 64 F)
 (atRecord : post.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMessage : post.locals.lookup (ofString "msg")=some (.val (.word message)))
 (memory : post.memory=s.memory) (globals : post.globals=s.globals)
 (domain : post.memaddrs=s.memaddrs) (code : post.code=s.code) :
 FrameNewTailContext post record message codePointer codeLength accessAddresses accessSlots empty frame scratch := by
 constructor
 · exact atRecord
 · exact atMessage
 · rw [globals];exact valid.atScratch
 · rw [globals];exact valid.atFrame
 · rw [globals];exact valid.atEmpty
 · exact valid.ordered
 · exact valid.scratchBelow
 · exact valid.recordBound
 · exact valid.beforeMessage
 · exact valid.messageBound
 · intro offset member;rw [domain];exact valid.messageDomain offset member
 · rw [memory];exact valid.codeAt
 · rw [memory];exact valid.lengthAt
 · rw [memory];exact valid.addressesAt
 · rw [memory];exact valid.slotsAt
 · exact valid.lengthBound
 · exact code.trans valid.sourceCode

theorem FrameNewTailContext.count_declaration_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (post : PanSemStateFiniteExact 64 F) (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (table : BitVec 64) (value : ValueHOL 64)
 (notRecord : name≠ofString "e") (notMessage : name≠ofString "msg")
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word table)])
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "htab_count") [argument] tail)=(some (.returned value),post)) :
 ∃count : BitVec 64,∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 FrameNewTailContext ready record message codePointer codeLength accessAddresses accessSlots empty frame scratch ∧
 ready.locals.lookup name=some (.val (.word count)) ∧ready.memory=s.memory ∧ready.globals=s.globals := by
 obtain ⟨count,bodyPost,output,tailRun,postEq,memory,globals,domain,endian,code⟩:=
  frame_new_count_declaration_returned s post name argument tail table value args valid.sourceCode run
 let ready:=setVarHOLFinite name (.val (.word count)) {bodyPost with locals:=s.locals}
 have atRecord : ready.locals.lookup (ofString "e")=some (.val (.word record)) := by
  simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notRecord] using valid.atRecord
 have atMessage : ready.locals.lookup (ofString "msg")=some (.val (.word message)) := by
  simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notMessage] using valid.atMessage
 have context:=valid.after_identity_frame ready atRecord atMessage memory globals domain code
 refine ⟨count,ready,output,tailRun,postEq,context,?_,memory,globals⟩
 simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem FrameNewTailContext.count_assignment_normal {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (post : PanSemStateFiniteExact 64 F) (name : MlS) (argument : ExpHOL 64) (table : BitVec 64)
 (notRecord : name≠ofString "e") (notMessage : name≠ofString "msg")
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word table)])
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "htab_count") [argument])=(none,post)) :
 ∃count : BitVec 64,post.locals.lookup name=some (.val (.word count)) ∧
 FrameNewTailContext post record message codePointer codeLength accessAddresses accessSlots empty frame scratch ∧
 post.memory=s.memory ∧post.globals=s.globals := by
 obtain ⟨count,atCount,other,memory,globals,domain,endian,code⟩:=frame_new_count_assignment_normal s post name argument table args valid.sourceCode run
 have atRecord : post.locals.lookup (ofString "e")=some (.val (.word record)):=
  (other (ofString "e") (Ne.symm notRecord)).trans valid.atRecord
 have atMessage : post.locals.lookup (ofString "msg")=some (.val (.word message)):=
  (other (ofString "msg") (Ne.symm notMessage)).trans valid.atMessage
 exact ⟨count,atCount,valid.after_identity_frame post atRecord atMessage memory globals domain code,memory,globals⟩

theorem FrameNewTailContext.message_load_arguments {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (offset word : BitVec 64) (member : offset∈([112,120,152,160] : List (BitVec 64)))
 (atWord : s.memory (message+offset)=.word word) :
 evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.load .one (frameNewLocalAddress (ofString "msg") offset)]=
 some [.val (.word word)] := by
 have address:=eval_frame_new_local_address s (ofString "msg") message offset valid.atMessage
 have evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (frameNewLocalAddress (ofString "msg") offset))=some (.val (.word word)) := by
  rw [evalHOLExact,address]
  have readable:=valid.messageDomain offset member
  simp [isWfShapeExactHOL,memLoadHOLExact,toExact,readable,atWord]
 simp only [evalListHOLFinite,evalListHOLExact,evaluated]
#print axioms FrameNewTailContext.after_identity_frame
#print axioms FrameNewTailContext.count_declaration_returned
#print axioms FrameNewTailContext.count_assignment_normal
#print axioms FrameNewTailContext.message_load_arguments
end InitECandidate.Runtime

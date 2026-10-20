import InitECandidate.Runtime.MptInsertExtensionComparison
import InitECandidate.Runtime.CommonPrefixNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual prefix comparison earns the clock needed by its selected
continuation. Both branches are extracted from the source condition, with
unchanged caller memory and metadata. -/
theorem mpt_insert_extension_comparison_normal_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (segment segmentLength key level length : BitVec 64)
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atSize : s.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (code : s.code=originalRuntimeCode)
 (budget : (wordMin segmentLength (length-level)).toNat+2≤s.clock)
 (run : evaluateHOLFiniteState s mptInsertExtensionComparison=(none,post)) :
 ∃found : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 found.toNat≤segmentLength.toNat ∧found.toNat≤(length-level).toNat ∧
 s.clock≤bodyPost.clock+(wordMin segmentLength (length-level)).toNat+2 ∧bodyPost.clock≤s.clock ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧
 bodyPost.be=s.be ∧bodyPost.code=s.code ∧
 (let ready:=setVarHOLFinite (ofString "pl") (.val (.word found)) {bodyPost with locals:=s.locals}
  evaluateHOLFiniteState ready
   (if found=segmentLength then mptInsertExtensionAdvance else mptInsertExtensionSplit)=(none,output)) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (ofString "pl",s.locals.lookup (ofString "pl"))} := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  mptInsertPrefixArguments=some [.val (.word segment),.val (.word segmentLength),
   .val (.word (key+level)),.val (.word (length-level))] := by
  simp [mptInsertPrefixArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atSegment,atSize,
   atKey,atLevel,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mptInsert_extension_comparison] at run
 obtain ⟨found,bodyPost,output,leftBound,rightBound,spent,remaining,memory,globals,domains,endian,installed,tail,scope⟩:=
  common_prefix_declaration_normal_frame s post (ofString "pl") mptInsertPrefixArguments
   mptInsertExtensionContinuation segment segmentLength (key+level) (length-level) args code budget run
 refine ⟨found,bodyPost,output,leftBound,rightBound,spent,remaining,memory,globals,domains,endian,installed,?_,scope⟩
 let ready:=setVarHOLFinite (ofString "pl") (.val (.word found)) {bodyPost with locals:=s.locals}
 have atFound : ready.locals.lookup (ofString "pl")=some (.val (.word found)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atLengthReady : ready.locals.lookup (ofString "sl")=some (.val (.word segmentLength)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atSize,show ofString "pl"≠ofString "sl" by decide]
 have cmp : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl")))=
  some (.val (.word (if found=segmentLength then 1#64 else 0#64))) := by
  simp [evalHOLExact,atFound,atLengthReady,Compiler.Encoders.Asm.wordCmpHOL]
 change evaluateHOLFiniteState ready mptInsertExtensionContinuation=(none,output) at tail
 rw [source_mptInsert_extension_continuation,evaluateHOLFiniteState_ite,cmp] at tail
 change evaluateHOLFiniteState ready (if found=segmentLength then _ else _)=(none,output)
 split <;> rename_i same
 · simpa only [if_pos same,show (1#64)≠0 from by decide,if_false] using tail
 · simpa only [if_neg same,show (0#64)=0 from rfl,ite_true] using tail

#print axioms mpt_insert_extension_comparison_normal_frame
end InitECandidate.Runtime

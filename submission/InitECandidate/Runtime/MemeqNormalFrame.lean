import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.PanThreeValueLookup
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.RlpWindowCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed declaration-call of the actual memeq exposes its scalar
result, read-only state, bounded clock consumption and scoped continuation.
Invalid reads remain possible; no equality result or readable-buffer oracle is assumed. -/
theorem memeq_declaration_normal_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (arguments : List (ExpHOL 64))
 (tail : ProgHOL 64) (a b size : BitVec 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word a),.val (.word b),.val (.word size)])
 (code : s.code=originalRuntimeCode) (small : size.toNat≤64) (budget : 4*size.toNat+1≤s.clock)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "memeq") arguments tail)=
  (none,post)) :
 ∃found : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 s.clock≤bodyPost.clock+4*size.toNat+1 ∧bodyPost.clock≤s.clock ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code ∧
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) {bodyPost with locals:=s.locals}) tail=
  (none,output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((HolFiniteMapExact.empty.update (ofString "a",.val (.word a))).update
   (ofString "b",.val (.word b))).update (ofString "n",.val (.word size))
 let entry:=callEntryStateHOLFinite s callee
 have localN : entry.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
 have installed : s.code.lookup (ofString "memeq")=some
  ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],
   sourceFunctionBody Guest.guestFn_memeq,.one) := by
  rw [code];exact originalRuntimeCode_memeq_lookup
 have lookup:=pan_three_value_lookup s.code.lookup (ofString "memeq")
  (ofString "a") (ofString "b") (ofString "n")
  (sourceFunctionBody Guest.guestFn_memeq) (.word a) (.word b) (.word size)
  (by decide) (by decide) (by decide) installed
 obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_normal_exact_scope
  s post name (ofString "memeq") .one .one arguments _
  (sourceFunctionBody Guest.guestFn_memeq) tail callee args lookup run
 obtain ⟨found,rfl⟩:=shapeWord_of_one checked.1
 obtain ⟨result,boundedPost,evaluated,spent,clock,notTimeout⟩:=
  evaluate_memeq_body64_bounded entry size localN small
   (by change 4*size.toNat≤s.clock-1;omega)
 have same:=Prod.mk.inj (evaluated.symm.trans bodyRun)
 have postSame : boundedPost=bodyPost:=same.2
 rw [postSame] at spent clock
 have memoryFrame:=evaluate_memeq_read_frame entry
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_memeq)
 rw [bodyRun] at memoryFrame metadata
 refine ⟨found,bodyPost,output,?_,?_,memoryFrame.1,memoryFrame.2,
  metadata.2.1,metadata.2.2.1,metadata.1,tailRun,scope⟩
 · change s.clock-1≤bodyPost.clock+4*size.toNat at spent
   omega
 · change bodyPost.clock≤s.clock-1 at clock
   omega

#print axioms memeq_declaration_normal_frame
end InitECandidate.Runtime

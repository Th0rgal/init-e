import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.CommonPrefixCallFrame
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual normally completed prefix declaration: real original body derives the common
prefix length bound, read-only state and consumed clock before the arbitrary
source continuation. No future-callee result or frame is assumed. -/
theorem common_prefix_declaration_normal_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (arguments : List (ExpHOL 64))
 (tail : ProgHOL 64) (a left b right : BitVec 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word a),.val (.word left),.val (.word b),.val (.word right)])
 (code : s.code=originalRuntimeCode) (budget : (wordMin left right).toNat+2≤s.clock)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "common_prefix_length") arguments tail)=
  (none,post)) :
 ∃found : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 found.toNat≤left.toNat ∧found.toNat≤right.toNat ∧
 s.clock≤bodyPost.clock+(wordMin left right).toNat+2 ∧bodyPost.clock≤s.clock ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code ∧
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) {bodyPost with locals:=s.locals}) tail=
  (none,output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 let callee:=commonPrefixCallee a left b right
 let entry:=callEntryStateHOLFinite s callee
 have leftAt : entry.locals.lookup (ofString "al")=some (.val (.word left)) := by
  simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,commonPrefixCallee,HolFiniteMapExact.lookup_update,FUPDATE]
 have rightAt : entry.locals.lookup (ofString "bl")=some (.val (.word right)) := by
  simp [entry,callEntryStateHOLFinite,callee,commonPrefixCallee,HolFiniteMapExact.lookup_update,FUPDATE]
 have installed : s.code.lookup (ofString "common_prefix_length")=some
  ([(ofString "a",.one),(ofString "al",.one),(ofString "b",.one),(ofString "bl",.one)],
   sourceFunctionBody Guest.guestFn_common_prefix_length,.one) := by
  rw [code];exact originalRuntimeCode_commonPrefix_lookup
 have lookup:=pan_four_word_lookup s.code.lookup (ofString "common_prefix_length")
  (ofString "a") (ofString "al") (ofString "b") (ofString "bl")
  (sourceFunctionBody Guest.guestFn_common_prefix_length) a left b right
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
 obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_normal_exact_scope
  s post name (ofString "common_prefix_length") .one .one arguments _
  (sourceFunctionBody Guest.guestFn_common_prefix_length) tail callee args lookup run
 obtain ⟨result,boundedPost,evaluated,spent,clock,notTimeout,property⟩:=
  evaluate_original_commonPrefix_body_bounded entry left right leftAt rightAt code
   (by change (wordMin left right).toNat+1≤s.clock-1;omega)
 have same:=Prod.mk.inj (evaluated.symm.trans bodyRun)
 obtain ⟨found,valueEq,leftBound,rightBound⟩:=property value same.1
 subst value
 have postSame : boundedPost=bodyPost:=same.2
 rw [postSame] at spent clock
 have memoryFrame:=evaluate_commonPrefix_body_read_frame entry left right leftAt rightAt code
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_common_prefix_length)
 rw [bodyRun] at memoryFrame metadata
 refine ⟨found,bodyPost,output,leftBound,rightBound,?_,?_,memoryFrame.1,memoryFrame.2,
  metadata.2.1,metadata.2.2.1,metadata.1,tailRun,scope⟩
 · change s.clock-1≤bodyPost.clock+(wordMin left right).toNat+1 at spent
   omega
 · change bodyPost.clock≤s.clock-1 at clock
   omega

#print axioms common_prefix_declaration_normal_frame
end InitECandidate.Runtime

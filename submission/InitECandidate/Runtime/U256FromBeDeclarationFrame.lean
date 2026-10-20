import InitECandidate.Runtime.U256FromBeBodyFrame
import InitECandidate.Runtime.OriginalU256FromBeCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.U256ZeroFundingValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual checked original conversion returns four word limbs, and its actual
same-run callee keeps all memory/globals at arbitrary fuel/read failures. -/
theorem u256_from_be_declaration_returned_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (arguments : List (ExpHOL 64))
 (tail : ProgHOL 64) (pointer length : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word pointer),.val (.word length)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "u256_from_be") arguments tail)=(some (.returned value),post)) :
 ∃a b c d : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (fundingU256 a b c d) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 have installed : s.code.lookup (ofString "u256_from_be")=some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_u256_from_be,.comb [.one,.one,.one,.one]) := by rw [code];exact originalRuntimeCode_u256FromBe_lookup
 have lookup:=pan_two_word_lookup_shape s.code.lookup (ofString "u256_from_be") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_u256_from_be) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=(HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "u256_from_be") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments _ _ tail callee value args lookup run
 obtain ⟨a,b,c,d,equal⟩:=value_four_words_of_checked_shape returned checked.1
 subst returned
 have frame:=u256FromBe_body_frame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_u256_from_be)
 rw [bodyRun] at frame metadata
 exact ⟨a,b,c,d,bodyPost,output,tailRun,scope,frame.1,frame.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms u256_from_be_declaration_returned_frame
end InitECandidate.Runtime

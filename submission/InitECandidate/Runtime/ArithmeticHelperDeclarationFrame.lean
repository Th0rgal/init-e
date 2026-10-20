import InitECandidate.Runtime.ArithmeticHelperFrame
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.U256ZeroFundingValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem arithmetic_two_u256_lookup {F : Type}
 (kind : ArithmeticOpcodeKind) (s : PanSemStateFiniteExact 64 F)
 (a b c d e f g h : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (arithmeticOpcodeHelper kind) [fundingU256 a b c d,fundingU256 e f g h]=
 some (arithmeticHelperBody kind,(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h),.comb [.one,.one,.one,.one]) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,arithmetic_helper_original_lookup kind,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kb : key=ofString "b"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · by_cases ka : key=ofString "a"
   · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
   · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kb,ka,Ne.symm kb,Ne.symm ka]
/-- Actual original helper declaration returns checked words and keeps all old
memory/globals. No arithmetic-result or callee-frame premise is supplied. -/
theorem arithmetic_helper_declaration_returned_frame {F : Type}
 (kind : ArithmeticOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,fundingU256 e f g h])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (arithmeticOpcodeHelper kind) arguments tail)=(some (.returned value),post)) :
 ∃r0 r1 r2 r3 : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (fundingU256 r0 r1 r2 r3) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (arithmeticOpcodeHelper kind) (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments _ _ tail callee value args (arithmetic_two_u256_lookup kind s a b c d e f g h code) run
 obtain ⟨r0,r1,r2,r3,equal⟩:=value_four_words_of_checked_shape returned checked.1
 subst returned
 have kept:=(arithmetic_helper_memory_frame kind) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (arithmeticHelperBody kind)
 rw [bodyRun] at kept metadata
 exact ⟨r0,r1,r2,r3,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms arithmetic_helper_declaration_returned_frame
end InitECandidate.Runtime

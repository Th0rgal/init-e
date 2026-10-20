import InitECandidate.Runtime.ShiftOpcodeSource
import InitECandidate.Runtime.ShiftHelperFrame
import InitECandidate.Runtime.VmFn_u256_signextend
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The real `u256_signextend` body. -/
def signextendHelperBody : ProgHOL 64 := sourceFunctionBody Guest.guestFn_u256_signextend

theorem signextend_helper_original_lookup :
 originalRuntimeCode.lookup (ofString "u256_signextend")=some ([(ofString "b",.one),(ofString "x",.comb [.one,.one,.one,.one])],signextendHelperBody,.comb [.one,.one,.one,.one]) := vmLookup_u256_signextend

/-- `u256_signextend` is in the kernel-checked read-only set. -/
theorem signextend_helper_memory_frame : MemoryFrame signextendHelperBody :=
 memoryFrame_of_good vmLookup_u256_signextend (by decide) (by decide)

private theorem signextend_two_lookup {F : Type}
 (s : PanSemStateFiniteExact 64 F) (bw : BitVec 64) (a b c d : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "u256_signextend") [.val (.word bw),fundingU256 a b c d]=
 some (signextendHelperBody,(HolFiniteMapExact.empty.update (ofString "b",.val (.word bw))).update (ofString "x",fundingU256 a b c d),.comb [.one,.one,.one,.one]) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,signextend_helper_original_lookup,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kx : key=ofString "x"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · by_cases kb : key=ofString "b"
   · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
   · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kx,kb,Ne.symm kx,Ne.symm kb]

/-- The actual original sign-extension helper declaration returns four checked
word limbs and keeps all old memory/globals; the argument list is the mixed
`[one word, four-limb struct]` signature of `u256_signextend`. -/
theorem signextend_helper_declaration_returned_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (bw : BitVec 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word bw),fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "u256_signextend") arguments tail)=(some (.returned value),post)) :
 ∃first second third fourth : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (fundingU256 first second third fourth) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "b",.val (.word bw))).update (ofString "x",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "u256_signextend") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments _ _ tail callee value args (signextend_two_lookup s bw a b c d code) run
 obtain ⟨first,second,third,fourth,equal⟩:=value_four_words_of_checked_shape returned checked.1
 have kept:=signextend_helper_memory_frame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) signextendHelperBody
 rw [bodyRun] at kept metadata
 rw [equal] at tailRun
 exact ⟨first,second,third,fourth,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms signextend_helper_declaration_returned_frame
end InitECandidate.Runtime

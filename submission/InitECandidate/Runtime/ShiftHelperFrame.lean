import InitECandidate.Runtime.ShiftOpcodeSource
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.VmFn_sat_word
import InitECandidate.Runtime.VmFn_u256_shl
import InitECandidate.Runtime.VmFn_u256_shr
import InitECandidate.Runtime.VmFn_u256_sar
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The real shift helper bodies, one per direct shift opcode. -/
def shiftHelperBody : ShiftOpcodeKind→ProgHOL 64
 | .shl=>sourceFunctionBody Guest.guestFn_u256_shl
 | .shr=>sourceFunctionBody Guest.guestFn_u256_shr
 | .sar=>sourceFunctionBody Guest.guestFn_u256_sar

/-- All four shift-family callees are in the kernel-checked read-only set. -/
theorem shift_helper_memory_frame (kind : ShiftOpcodeKind) : MemoryFrame (shiftHelperBody kind) := by
 cases kind with
 | shl=>exact memoryFrame_of_good vmLookup_u256_shl (by decide) (by decide)
 | shr=>exact memoryFrame_of_good vmLookup_u256_shr (by decide) (by decide)
 | sar=>exact memoryFrame_of_good vmLookup_u256_sar (by decide) (by decide)

theorem shift_amount_original_lookup :
 originalRuntimeCode.lookup (ofString "sat_word")=some ([(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_sat_word,.one) := vmLookup_sat_word

theorem shift_amount_memory_frame : MemoryFrame (sourceFunctionBody Guest.guestFn_sat_word) :=
 memoryFrame_of_good vmLookup_sat_word (by decide) (by decide)

theorem shift_helper_original_lookup (kind : ShiftOpcodeKind) :
 originalRuntimeCode.lookup (shiftOpcodeHelper kind)=some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "n",.one)],shiftHelperBody kind,.comb [.one,.one,.one,.one]) := by
 cases kind with
 | shl=>exact vmLookup_u256_shl
 | shr=>exact vmLookup_u256_shr
 | sar=>exact vmLookup_u256_sar

private theorem shift_amount_lookup {F : Type}
 (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "sat_word") [fundingU256 a b c d]=
 some (sourceFunctionBody Guest.guestFn_sat_word,(HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d)),.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,shift_amount_original_lookup,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kv : key=ofString "v"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kv,Ne.symm kv]

private theorem shift_two_lookup {F : Type} (kind : ShiftOpcodeKind)
 (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64) (n : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (shiftOpcodeHelper kind) [fundingU256 a b c d,.val (.word n)]=
 some (shiftHelperBody kind,(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "n",.val (.word n)),.comb [.one,.one,.one,.one]) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,shift_helper_original_lookup kind,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kn : key=ofString "n"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · by_cases ka : key=ofString "a"
   · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
   · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kn,ka,Ne.symm kn,Ne.symm ka]

/-- A checked one-word value is a concrete word. -/
private theorem value_word_of_checked_one (value : ValueHOL 64)
 (checked : shapeEqHOL (shapeOfHOLExact value) .one = true) :
 ∃word : BitVec 64, value=.val (.word word) := by
 have shape := (shapeEqHOL_eq_true _ _).mp checked
 cases value with
 | val atom => cases atom with | word word => exact ⟨word,rfl⟩
 | rStruct fields => simp [shapeOfHOLExact] at shape
 | nStruct name fields => simp [shapeOfHOLExact] at shape

/-- The real `sat_word` declaration returns a checked word and keeps all old
memory/globals, from the checked four-limb argument. -/
theorem shift_amount_declaration_returned_word {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "sat_word") arguments tail)=(some (.returned value),post)) :
 ∃word : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "sat_word") .one .one arguments _ _ tail callee value args (shift_amount_lookup s a b c d code) run
 obtain ⟨word,equal⟩:=value_word_of_checked_one returned checked.1
 have kept:=shift_amount_memory_frame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_sat_word)
 rw [bodyRun] at kept metadata
 rw [equal] at tailRun
 exact ⟨word,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms shift_amount_declaration_returned_word

/-- The actual original shift-helper declaration returns four checked word limbs
and keeps all old memory/globals; the argument list is the mixed
`[four-limb struct, one word]` signature of `u256_shl/shr/sar`. -/
theorem shift_helper_declaration_returned_frame {F : Type}
 (kind : ShiftOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d : BitVec 64) (n : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,.val (.word n)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (shiftOpcodeHelper kind) arguments tail)=(some (.returned value),post)) :
 ∃first second third fourth : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (fundingU256 first second third fourth) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "n",.val (.word n))
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (shiftOpcodeHelper kind) (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments _ _ tail callee value args (shift_two_lookup kind s a b c d n code) run
 obtain ⟨first,second,third,fourth,equal⟩:=value_four_words_of_checked_shape returned checked.1
 have kept:=shift_helper_memory_frame kind (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (shiftHelperBody kind)
 rw [bodyRun] at kept metadata
 rw [equal] at tailRun
 exact ⟨first,second,third,fourth,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms shift_helper_declaration_returned_frame
end InitECandidate.Runtime


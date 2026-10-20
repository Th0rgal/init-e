import InitECandidate.Runtime.ComparisonOpcodeSource
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.U256ZeroFundingValue
import InitECandidate.Runtime.VmFn_u256_lt
import InitECandidate.Runtime.VmFn_u256_gt
import InitECandidate.Runtime.VmFn_u256_eq
import InitECandidate.Runtime.VmFn_u256_is_zero
import InitECandidate.Runtime.GlobalKeepAllProgram
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

/-- The real comparison helper bodies, one per direct comparison opcode. -/
def comparisonHelperBody : ComparisonOpcodeKind→ProgHOL 64
 | .lt=>sourceFunctionBody Guest.guestFn_u256_lt
 | .gt=>sourceFunctionBody Guest.guestFn_u256_gt
 | .eq=>sourceFunctionBody Guest.guestFn_u256_eq

theorem comparison_helper_original_lookup (kind : ComparisonOpcodeKind) :
 originalRuntimeCode.lookup (comparisonOpcodeHelper kind)=some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],comparisonHelperBody kind,.one) := by
 cases kind with
 | lt=>exact vmLookup_u256_lt
 | gt=>exact vmLookup_u256_gt
 | eq=>exact vmLookup_u256_eq

/-- Every real comparison helper body is read-only: memory and globals are
kept at every clock and every outcome. -/
theorem comparison_helper_memory_frame (kind : ComparisonOpcodeKind) : MemoryFrame (comparisonHelperBody kind) := by
 cases kind with
 | lt=>exact memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)
 | gt=>exact memoryFrame_of_good vmLookup_u256_gt (by decide) (by decide)
 | eq=>exact memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)

def zeroHelperBody : ProgHOL 64:=sourceFunctionBody Guest.guestFn_u256_is_zero

theorem zero_helper_original_lookup : originalRuntimeCode.lookup zeroOpcodeHelper=some ([(ofString "a",.comb [.one,.one,.one,.one])],zeroHelperBody,.one) := vmLookup_u256_is_zero

theorem zero_helper_memory_frame : MemoryFrame zeroHelperBody :=
 memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)

private theorem comparison_two_u256_lookup {F : Type}
 (kind : ComparisonOpcodeKind) (s : PanSemStateFiniteExact 64 F)
 (a b c d e f g h : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (comparisonOpcodeHelper kind) [fundingU256 a b c d,fundingU256 e f g h]=
 some (comparisonHelperBody kind,(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h),.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,comparison_helper_original_lookup kind,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kb : key=ofString "b"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · by_cases ka : key=ofString "a"
   · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
   · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kb,ka,Ne.symm kb,Ne.symm ka]

private theorem zero_one_u256_lookup {F : Type}
 (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup zeroOpcodeHelper [fundingU256 a b c d]=
 some (zeroHelperBody,(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)),.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,zero_helper_original_lookup,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases ka : key=ofString "a"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,ka,Ne.symm ka]

/-- A checked one-word value is a concrete word: the exact atom carrier has
only the `.word` constructor, and `rStruct`/`nStruct` have non-`.`one` shapes. -/
private theorem value_word_of_checked_one (value : ValueHOL 64)
 (checked : shapeEqHOL (shapeOfHOLExact value) .one = true) :
 ∃word : BitVec 64, value=.val (.word word) := by
 have shape := (shapeEqHOL_eq_true _ _).mp checked
 cases value with
 | val atom => cases atom with | word word => exact ⟨word,rfl⟩
 | rStruct fields => simp [shapeOfHOLExact] at shape
 | nStruct name fields => simp [shapeOfHOLExact] at shape

/-- Actual original comparison-helper declaration returns a checked word and
keeps all old memory/globals. No helper-result or callee-frame premise is
supplied: the two checked four-limb struct arguments flow into the real
callee entry state. -/
theorem comparison_helper_declaration_returned_word {F : Type}
 (kind : ComparisonOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,fundingU256 e f g h])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (comparisonOpcodeHelper kind) arguments tail)=(some (.returned value),post)) :
 ∃word : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (comparisonOpcodeHelper kind) .one .one arguments _ _ tail callee value args (comparison_two_u256_lookup kind s a b c d e f g h code) run
 obtain ⟨word,equal⟩:=value_word_of_checked_one returned checked.1
 have kept:=(comparison_helper_memory_frame kind) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (comparisonHelperBody kind)
 rw [bodyRun] at kept metadata
 rw [equal] at tailRun
 exact ⟨word,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩

/-- Same for the real `u256_is_zero` helper, whose single checked four-limb
struct argument flows into the callee entry state. -/
theorem zero_helper_declaration_returned_word {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one zeroOpcodeHelper arguments tail)=(some (.returned value),post)) :
 ∃word : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name zeroOpcodeHelper .one .one arguments _ _ tail callee value args (zero_one_u256_lookup s a b c d code) run
 obtain ⟨word,equal⟩:=value_word_of_checked_one returned checked.1
 have kept:=zero_helper_memory_frame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) zeroHelperBody
 rw [bodyRun] at kept metadata
 rw [equal] at tailRun
 exact ⟨word,bodyPost,output,tailRun,scope,kept.1,kept.2,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms comparison_helper_original_lookup
#print axioms comparison_helper_memory_frame
#print axioms comparison_helper_declaration_returned_word
#print axioms zero_helper_declaration_returned_word
end InitECandidate.Runtime

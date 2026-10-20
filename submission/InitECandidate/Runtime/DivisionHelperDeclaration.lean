import InitECandidate.Runtime.DivisionSignedWindow
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.DivisionOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem division_helper_original_lookup (kind : DivisionOpcodeKind) :
 originalRuntimeCode.lookup (divisionOpcodeHelper kind)=some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],divisionHelperBody kind,.comb [.one,.one,.one,.one]) := by
 cases kind with
 | div=>exact vmLookup_u256_div
 | sdiv=>exact vmLookup_u256_sdiv
 | mod=>exact vmLookup_u256_mod
 | smod=>exact vmLookup_u256_smod

private theorem division_two_u256_lookup {F : Type} (kind : DivisionOpcodeKind)
 (s : PanSemStateFiniteExact 64 F) (a b c d e f g h : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (divisionOpcodeHelper kind) [fundingU256 a b c d,fundingU256 e f g h]=
 some (divisionHelperBody kind,(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h),.comb [.one,.one,.one,.one]) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,division_helper_original_lookup kind,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases kb : key=ofString "b"
 · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
 · by_cases ka : key=ofString "a"
   · subst key;simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256]
   · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,fundingU256,kb,ka,Ne.symm kb,Ne.symm ka]

/-- The actual original division-helper declaration returns four checked word
limbs and keeps memory outside the `u256_ws` workspace plus every global. No
callee-frame premise is supplied: the two checked four-limb arguments flow into
the real callee entry state, and the window comes from the helper's own proof. -/
theorem division_helper_declaration_returned_frame {F : Type}
 (kind : DivisionOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64) (U : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,fundingU256 e f g h])
 (code : s.code=originalRuntimeCode)
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (domOK : DomOK s.memaddrs) (hU : U.toNat+640≤2^64)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (divisionOpcodeHelper kind) arguments tail)=(some (.returned value),post)) :
 ∃first second third fourth : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 (∀watched : BitVec 64,¬ WS U watched→bodyPost.memory watched=s.memory watched) ∧
 bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "b",fundingU256 e f g h)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (divisionOpcodeHelper kind) (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments _ _ tail callee value args (division_two_u256_lookup kind s a b c d e f g h code) run
 obtain ⟨first,second,third,fourth,equal⟩:=value_four_words_of_checked_shape returned checked.1
 have memory : ∀watched : BitVec 64,¬ WS U watched→bodyPost.memory watched=s.memory watched := by
  intro watched hw
  have step:=division_helper_memory_outside_window kind (callEntryStateHOLFinite s callee) U watched (by exact code) (by exact domOK) (by exact ws) hU hw
  rw [bodyRun] at step
  exact step
 have globals:=division_helper_globals_frame kind (callEntryStateHOLFinite s callee) (by exact code)
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (divisionHelperBody kind)
 rw [bodyRun] at globals metadata
 rw [equal] at tailRun
 exact ⟨first,second,third,fourth,bodyPost,output,tailRun,scope,memory,globals,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms division_helper_declaration_returned_frame
end InitECandidate.Runtime

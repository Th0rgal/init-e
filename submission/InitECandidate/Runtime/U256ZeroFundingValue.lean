import InitECandidate.Runtime.MessageCallGasReturnedCeiling
import InitECandidate.Runtime.VmFn_u256_is_zero
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def fundingU256 (a b c d : BitVec 64) : ValueHOL 64:=.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]
def fundingU256ZeroFlag (a b c d : BitVec 64) : BitVec 64:=if a|||b|||c|||d=0 then 1 else 0

theorem funding_u256_is_zero_result {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64)
 (atArgument : s.locals.lookup (ofString "a")=some (fundingU256 a b c d)) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_is_zero)).1=some (.returned (.val (.word (fundingU256ZeroFlag a b c d)))) := by
 have source : sourceFunctionBody Guest.guestFn_u256_is_zero=.seq
  (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),.rfield 1 (.var .local (ofString "a")),.rfield 2 (.var .local (ofString "a")),.rfield 3 (.var .local (ofString "a"))]) (.const 0)) (.return (.const 1)) .skip)
  (.return (.const 0)) := by rw [sourceFunctionBody_eq_structural];rfl
 rw [source,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite]
 have orDef (x y : BitVec 64) : OrOp.or x y=x|||y:=rfl
 by_cases zero : a|||b|||c|||d=0
 all_goals have normalized:=zero
 all_goals first | change a|||b|||c|||d=0#64 at normalized | change ¬a|||b|||c|||d=0#64 at normalized
 all_goals simp only [BitVec.or_eq_zero_iff,and_assoc] at normalized
 all_goals simp [evalHOLExact,evalListHOLExact,atArgument,fundingU256,wordOpHOL,wordOp,valueIsWord,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,fixClockHOLFinite,shapeOfHOLExact,sizeOfShapeWithContextHOL,fundingU256ZeroFlag,zero,BitVec.or_assoc,orDef,normalized]

theorem funding_single_u256_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64)
 (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "u256_is_zero") [fundingU256 a b c d]=
 some (sourceFunctionBody Guest.guestFn_u256_is_zero,HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d),.one) := by
 apply lookupCodeFinite_of_exact
 have installed:=vmLookup_u256_is_zero
 rw [code]
 simp [lookupCodeHOLExact,installed,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases same : key=ofString "a"
 · subst key;simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,same,Ne.symm same]

/-- Both the caller's earlier value test and the gas calculator's value test
can use this exact actual result, so stipend funding is tied to the same value. -/
theorem funding_u256_zero_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) [argument]=some [fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "u256_is_zero") [argument] tail)=(some (.returned value),post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (fundingU256ZeroFlag a b c d))) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧bodyPost.code=s.code := by
 let callee:=HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "u256_is_zero") .one .one [argument] [fundingU256 a b c d] (sourceFunctionBody Guest.guestFn_u256_is_zero) tail callee value args (funding_single_u256_lookup s a b c d code) run
 have atArgument : (callEntryStateHOLFinite s callee).locals.lookup (ofString "a")=some (fundingU256 a b c d) := by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have result:=funding_u256_is_zero_result (callEntryStateHOLFinite s callee) a b c d atArgument
 rw [bodyRun] at result
 have returnedEq : returned=.val (.word (fundingU256ZeroFlag a b c d)):=PanSemResultExact.returned.inj (Option.some.inj result)
 subst returned
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_u256_is_zero)
 rw [bodyRun] at metadata
 exact ⟨bodyPost,output,tailRun,postEq,metadata.1⟩
#print axioms funding_u256_is_zero_result
#print axioms funding_single_u256_lookup
#print axioms funding_u256_zero_declaration_returned
end InitECandidate.Runtime

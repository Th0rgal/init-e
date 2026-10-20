import InitECandidate.Runtime.RlpPutU256CheckedDeclaration
import InitECandidate.Runtime.U256FromBeDeclarationFrame
import InitECandidate.Runtime.U256FromBeBodyBound
import InitECandidate.Runtime.EvmMemoryOperandContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual checked read of 32 bytes, including failed reads. The concrete
physical continuation is needed only for real checked four-limb returns. -/
theorem runBounded_u256_read32_physical_declaration {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words) (name : MlS) (pointer : BitVec 64)
 (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (cost : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer),.val (.word 32)])
 (code : s.code=originalRuntimeCode) (budget : 32+1+cost≤s.clock)
 (resume : ∀(a b c d : BitVec 64) (ready : PanSemStateFiniteExact 64 F),
  ready.locals.lookup name=some (fundingU256 a b c d) →
  EvmMemoryOperandAt ready frame words → ready.code=originalRuntimeCode →
  cost≤ready.clock → RunBounded ready tail cost) :
 RunBounded s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "u256_from_be") arguments tail) (32+1+cost) := by
 apply runBounded_checked_declaration s name (ofString "u256_from_be") (.comb [.one,.one,.one,.one]) arguments tail 32 cost budget
 intro values body callee returnShape actualArgs found
 have same : values=[.val (.word pointer),.val (.word 32)]:=Option.some.inj (actualArgs.symm.trans args)
 subst values
 have installed : s.code.lookup (ofString "u256_from_be")=some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_u256_from_be,.comb [.one,.one,.one,.one]) := by rw [code];exact originalRuntimeCode_u256FromBe_lookup
 have lookup:=pan_two_word_lookup_shape s.code.lookup (ofString "u256_from_be") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_u256_from_be) (.comb [.one,.one,.one,.one]) pointer 32 (by decide) installed
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 let entry:=callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word 32)))
 have pAt : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have nAt : entry.locals.lookup (ofString "n")=some (.val (.word 32)) := by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 constructor
 · have bounded:=evaluate_u256FromBe_body_bounded entry pointer 32 32 pAt nAt code (by decide) (by decide) (by change 32≤s.clock-1;omega)
   exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩
 · intro value post returned checked remaining
   have pair:=checked
   simp only [Bool.and_eq_true] at pair
   obtain ⟨a,b,c,d,equal⟩:=value_four_words_of_checked_shape value pair.1
   subst value
   have frameKept:=u256FromBe_body_frame entry code
   have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_u256_from_be)
   rw [returned] at frameKept metadata
   let ready:=setVarHOLFinite name (fundingU256 a b c d) {post with locals:=s.locals}
   have physical : EvmMemoryOperandAt ready frame words:=valid.after_context frameKept.2 frameKept.1 metadata.2.1
   exact resume a b c d ready (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) physical (metadata.1.trans code) remaining
#print axioms runBounded_u256_read32_physical_declaration
end InitECandidate.Runtime

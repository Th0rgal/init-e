import InitECandidate.Runtime.ArithmeticHelperFrame
import InitECandidate.Runtime.ArithmeticPushRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual finite-family pure helper followed by real no-growth push and PC.
Invalid arguments or helper returns cannot force additional execution. -/
theorem arithmetic_helper_tail_bounded {F : Type}
 (kind : ArithmeticOpcodeKind) (s : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : arithmeticOpcodeHelperCost kind+1+2≤s.clock) :
 RunBounded s (arithmeticOpcodeAt kind 3) (arithmeticOpcodeHelperCost kind+1+2) := by
 rw [source_arithmetic_opcode_3 kind]
 let arguments : List (ExpHOL 64):=[.var .local (ofString "x"),.var .local (ofString "y")]
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>unfold RunBounded;rw [evaluateHOLFiniteState_decCall_total,args];simp
 | some values=>
  apply RunBounded.decCall (bodyCost:=arithmeticOpcodeHelperCost kind) (tailCost:=2) args budget
  intro body callee returnShape found
  have bounded:=ProgBounded.bodies_of_fun (arithmetic_opcode_helper_bounded kind) s code (by omega) values body callee returnShape found
  have installed : s.code.lookup (arithmeticOpcodeHelper kind)=some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],arithmeticHelperBody kind,.comb [.one,.one,.one,.one]) := by rw [code];exact arithmetic_helper_original_lookup kind
  have bodyEq:=lookupCodeHOLFinite_installed_body s.code.lookup (arithmeticOpcodeHelper kind) _ (arithmeticHelperBody kind) body _ returnShape values callee installed found
  subst body
  refine ⟨bounded,?_⟩
  intro value post returned remaining
  have kept:=(arithmetic_helper_memory_frame kind) (callEntryStateHOLFinite s callee) code
  have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (arithmeticHelperBody kind)
  rw [returned] at kept metadata
  let ready:=setVarHOLFinite (ofString "r") value {post with locals:=s.locals}
  have physical : EvmMemoryOperandAt ready frame words:=valid.after_context kept.2 kept.1 metadata.2.1
  exact arithmetic_push_tail_bounded kind ready frame words physical inside (metadata.1.trans code) remaining
#print axioms arithmetic_helper_tail_bounded
end InitECandidate.Runtime

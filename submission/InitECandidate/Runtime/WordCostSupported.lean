import InitECandidate.Runtime.WordStackRefinedLeaf
import InitECandidate.Runtime.WordFrameMapConst
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordProps Flapjack.WordSemStateFiniteExact

/-- Syntax covered by the executed compiler-cost proof. This is checked on
the actual program and declaration table; unsupported primitives are explicit. -/
def wordCostSupported : WordLangProgHOL (BitVec 64) → Bool
  | .seq first second => wordCostSupported first && wordCostSupported second
  | .ite _ _ _ first second => wordCostSupported first && wordCostSupported second
  | .loop _ body _ | .mustTerminate body => wordCostSupported body
  | .call ret _ _ handler =>
      (match ret with | none => true | some (_,_,body,_,_) => wordCostSupported body) &&
      (match handler with | none => true | some (_,body,_,_) => wordCostSupported body)
  | p => (refinedWordStackLeafBudget p).isSome

theorem wordCostSupported_noInstall (program : WordLangProgHOL (BitVec 64))
    (supported : wordCostSupported program = true) : noInstallSubprogsHOL program = true := by
  fun_induction wordCostSupported program <;>
    simp_all [wordCostSupported,refinedWordStackLeafBudget,noInstallSubprogsHOL,
      notCreatedSubprogsWithMemOp]
  case case5 ret dest args handler ihRet ihHandler =>
    cases ret <;> cases handler <;>
      simp_all [wordCostSupported,refinedWordStackLeafBudget,noInstallSubprogsHOL,
        notCreatedSubprogsWithMemOp]
  case case6 program notSeq notIte notLoop notMt notCall =>
    cases program <;>
      simp_all [wordCostSupported,refinedWordStackLeafBudget,noInstallSubprogsHOL,
        notCreatedSubprogsWithMemOp]

/-- Every code lookup must have a supported body, including indirect callees. -/
def CostSupportedCode (code : Spt (Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  ∀ key arity program, sptLookup key code = some (arity,program) → wordCostSupported program = true

theorem CostSupportedCode.noInstallCode
    {code : Spt (Nat × WordLangProgHOL (BitVec 64))} (supported : CostSupportedCode code) :
    noInstallCode code := by
  intro key arity program found
  exact wordCostSupported_noInstall program (supported key arity program found)

theorem CostSupportedCode.findCode {C F : Type}
    {source : WordSemStateFiniteExact 64 C F} (supported : CostSupportedCode source.code)
    (dest : Option Nat) (args args1 : List (WordLocW 64))
    (program : WordLangProgHOL (BitVec 64)) (size : Option Nat)
    (found : wordSemFindCode dest args source.code source.stackSize = some (args1,program,size)) :
    wordCostSupported program = true := by
  obtain ⟨key,arity,lookup⟩ := findCode_lookup source.code dest args source.stackSize args1 program size found
  exact supported key arity program lookup

theorem CostSupportedCode.after_evaluate {C F : Type}
    {program : WordLangProgHOL (BitVec 64)} {source post : WordSemStateFiniteExact 64 C F}
    {result : Option (WordSemResult 64)}
    (codeSupported : CostSupportedCode source.code)
    (supported : wordCostSupported program = true)
    (run : evaluate program source = (result,post)) : CostSupportedCode post.code := by
  have same := code_evaluate program source (wordCostSupported_noInstall program supported)
    codeSupported.noInstallCode
  rw [run] at same
  exact same ▸ codeSupported

#print axioms wordCostSupported_noInstall
#print axioms CostSupportedCode.noInstallCode
#print axioms CostSupportedCode.findCode
#print axioms CostSupportedCode.after_evaluate
end InitECandidate.Runtime.WordToStack

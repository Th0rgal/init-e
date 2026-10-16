import InitECandidate.Runtime.StackCodeSize
import InitECandidate.Runtime.StackRemoveWork

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Installation cannot grow the bitmap table when every oracle payload is empty. -/
structure EmptyBitmapOracle {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop where
  empty : ∀ n, (s.compileOracle n).2.2 = []

theorem EmptyBitmapOracle.of_evaluate {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {s post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)}
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (oracle : EmptyBitmapOracle s) :
    EmptyBitmapOracle post ∧ post.bitmaps = s.bitmaps := by
  obtain ⟨count, shifted, _, bitmaps⟩ :=
    Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p s result post run
  constructor
  · constructor
    intro n
    rw [shifted]
    exact oracle.empty (n + count)
  · rw [bitmaps]
    have empty : ((List.range count).map (fun n => (s.compileOracle n).2.2)).flatten = [] := by
      simp [oracle.empty]
    rw [empty, List.append_nil]

theorem EmptyBitmapOracle.withClock {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} (oracle : EmptyBitmapOracle s) (fuel : Nat) :
    EmptyBitmapOracle {s with clock := fuel} := ⟨oracle.empty⟩

/-- The bitmap-copy allowance is a fixed constant along every actual execution
from an empty-payload oracle, including executions that finish with an error. -/
theorem storeConsts_work_invariant {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {s post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)}
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (oracle : EmptyBitmapOracle s)
    (a b c : Nat) :
    removeWork (.storeConsts a b c) post = 2 + (2 ^ width + 1) * s.bitmaps.length := by
  rw [removeWork, (oracle.of_evaluate run).2]

#print axioms EmptyBitmapOracle.of_evaluate
#print axioms storeConsts_work_invariant
end InitECandidate.Runtime.StackRemove

import InitECandidate.Runtime.SelectedStackFields
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- The original initializer preserves word-valued memory over its selected
heap domain. Its complete original initializer hypotheses are retained. -/
theorem selected_heap_memory_words {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (s : StackSemStateFiniteExact width C F) (jump : Bool) (bounds : BitVec width × BitVec width)
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hyp : InitCodePre.initCodePre pointer bitmaps dataSpace s ∧
      codeRelHOL jump bounds pointer code s.code ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i,p) ∈ (oracle n).2.1 →
        Flapjack.Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      maxStackAlloc ≤ maxHeap)
    (words : ∀ address, ∃ word, s.memory address = WordLocW.word word)
    (post : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s = some post) :
    ∀ address, post.mdomain address = true → ∃ word, post.memory address = WordLocW.word word := by
  have initialized := InitCodeCorrect.initCodeThm generateGc maxHeap pointer bitmaps dataSpace s jump bounds code oracle hyp
  cases run : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer,s) with
  | mk result t =>
    rw [run] at initialized
    cases result with
    | some value => exact False.elim initialized
    | none =>
      unfold InitMake.makeInitOpt at selected
      rw [run] at selected
      dsimp only at selected
      split at selected
      · have same := Option.some.inj selected
        subst post
        intro address valid
        have frame := initialized.2.2.2.2.2.2
        have member : SetSep.fun2Set
            (s.memory,fun a => (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t).mdomain a = true)
            (address,s.memory address) := ⟨address,valid,rfl⟩
        rw [frame] at member
        have equal := (SetSep.fun2SetThm t.memory _ address (s.memory address)).mp member
        obtain ⟨word,found⟩ := words address
        exact ⟨word,equal.1.trans found⟩
      · cases selected

#print axioms selected_heap_memory_words
end InitECandidate.Runtime.StackRemove

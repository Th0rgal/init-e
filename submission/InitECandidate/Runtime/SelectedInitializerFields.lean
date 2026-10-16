import InitECandidate.Runtime.SelectedHeapMemoryWords
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Original initializer execution preserves FFI and installs the initial
heap-pointer register as CurrHeap, without an assumed initializer run. -/
theorem selected_initializer_fields {width : Nat} [NeZero width] {C F : Type}
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
    (post : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s = some post) :
    post.ffi = s.ffi ∧ post.store.lookup .currHeap = s.regs.lookup 2 := by
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
        obtain ⟨base,other,top,before,_,after,_⟩ := initialized.1
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,heapLink,_⟩ := initialized.2.1
        exact ⟨initialized.2.2.1,heapLink.symm.trans (after.trans before.symm)⟩
      · cases selected


#print axioms selected_initializer_fields
end InitECandidate.Runtime.StackRemove

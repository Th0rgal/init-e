import InitECandidate.Runtime.SelectedStackFields
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

theorem selected_clock_le {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (initial source : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt gc maxHeap bitmaps dataSpace oracle jump bounds pointer code initial = some source) :
    source.clock ≤ initial.clock := by
  cases run : StackSemEvaluate.evaluate (initCode gc maxHeap pointer,initial) with
  | mk result t =>
    unfold InitMake.makeInitOpt at selected
    rw [run] at selected
    cases result with
    | some value => cases selected
    | none =>
      dsimp only at selected
      split at selected
      · cases Option.some.inj selected
        exact StackSemEvaluateClock.evaluateClock (initCode gc maxHeap pointer) initial none t run
      · cases selected

#print axioms selected_clock_le
end InitECandidate.Runtime.StackRemove

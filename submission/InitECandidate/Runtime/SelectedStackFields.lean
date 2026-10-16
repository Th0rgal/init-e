import Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Successful optional initialization installs the exact supplied code, bitmap
list, and oracle. These field identities require no semantic assumptions. -/
theorem selected_fields {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (initial source : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt gc maxHeap bitmaps dataSpace oracle jump bounds pointer code initial = some source) :
    source.code = code ∧ source.bitmaps = bitmaps ∧ source.compileOracle = oracle := by
  unfold InitMake.makeInitOpt at selected
  split at selected
  · cases selected
  · split at selected
    · cases Option.some.inj selected
      exact ⟨rfl,rfl,rfl⟩
    · cases selected

#print axioms selected_fields
end InitECandidate.Runtime.StackRemove

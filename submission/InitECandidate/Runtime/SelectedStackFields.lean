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

/-- Successful optional initialization certifies word-valued heap registers
in its store; the result follows from the original initProp guard. -/
theorem selected_heap_words {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (initial source : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt gc maxHeap bitmaps dataSpace oracle jump bounds pointer code initial = some source) :
    ∃ current capacity : BitVec width, source.store.lookup .currHeap = some (.word current) ∧
      source.store.lookup .heapLength = some (.word capacity) := by
  unfold InitMake.makeInitOpt at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i ready evaluated valid
      obtain ⟨current,other,bitmap,length,heap,_,_,_,_,_,capacity,_⟩ := valid
      cases Option.some.inj selected
      exact ⟨current,_,heap,capacity⟩
    · cases selected

#print axioms selected_heap_words
#print axioms selected_fields
end InitECandidate.Runtime.StackRemove

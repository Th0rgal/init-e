import InitECandidate.Proofs.Op5.StackRemoveArena

namespace InitE.Op5

/-- Re-export of the `StackRemove` state relation bridge over disjoint scratch ownership. -/
theorem stackRemoveScratchStateRel {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : Flapjack.StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop)
    (rel : Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target)
    (disjoint : ∀ a, ¬ (arena a ∧ target.mdomain a = true))
    (agree : ∀ a, arena a → source.memory a = target.memory a) :
    Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer
      (withArena arena source) (withArena arena target) :=
  stackRemove_stateRel_withArena jump bounds pointer source target arena rel disjoint agree

end InitE.Op5

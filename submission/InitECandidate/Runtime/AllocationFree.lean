import Flapjack.Compiler.Backend.StackAlloc.Compile

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Syntax for which allocation lowering introduces no stub calls or labels. -/
def allocationFree {width : Nat} [NeZero width] (prog : HolProg width) : Bool :=
  match prog with
  | .seq a b | .ite _ _ _ a b => allocationFree a && allocationFree b
  | .loop body => allocationFree body
  | .call none _ none => true
  | .call none _ (some _) => false
  | .call (some (rp, _, _, _)) _ none => allocationFree rp
  | .call (some (rp, _, _, _)) _ (some (hp, _, _)) => allocationFree rp && allocationFree hp
  | .alloc _ | .storeConsts _ _ (some _) => false
  | _ => true
termination_by sizeOf prog

/-- Allocation-free syntax is unchanged by the actual compiler, including
its next-label counter. -/
theorem allocationFree_comp {width : Nat} [NeZero width] (n m : Nat) (prog : HolProg width)
    (free : allocationFree prog = true) :
    Flapjack.Compiler.Backend.StackAlloc.comp n m prog = (prog, m) := by
  fun_induction Flapjack.Compiler.Backend.StackAlloc.comp n m prog
  all_goals simp_all [allocationFree]
  all_goals rename_i counter dest handler; cases handler <;> simp_all [allocationFree]

def allocationFreeCode {width : Nat} [NeZero width] (code : List (Nat × HolProg width)) : Bool :=
  code.all (fun entry => allocationFree entry.2)

theorem allocationFreeCode_append {width : Nat} [NeZero width] (a b : List (Nat × HolProg width)) :
    allocationFreeCode (a ++ b) = (allocationFreeCode a && allocationFreeCode b) := by
  simp [allocationFreeCode]

theorem allocationFreeCode_map {width : Nat} [NeZero width] (code : List (Nat × HolProg width))
    (free : allocationFreeCode code = true) :
    code.map Flapjack.Compiler.Backend.StackAlloc.progComp = code := by
  induction code with
  | nil => rfl
  | cons entry rest ih =>
    have parts : allocationFree entry.2 = true ∧ allocationFreeCode rest = true := by
      simpa [allocationFreeCode] using free
    rcases entry with ⟨n, body⟩
    simp only [List.map_cons, Flapjack.Compiler.Backend.StackAlloc.progComp,
      allocationFree_comp n _ body parts.1, ih parts.2]

theorem allocationFree_compile {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (code : List (Nat × HolProg width))
    (free : allocationFreeCode code = true) :
    Flapjack.Compiler.Backend.StackAlloc.compile conf code =
      Flapjack.Compiler.Backend.StackAlloc.stubs conf ++ code := by
  simp only [Flapjack.Compiler.Backend.StackAlloc.compile, allocationFreeCode_map code free]

#print axioms allocationFree_compile

#print axioms allocationFree_comp
end InitECandidate.Runtime.StackAlloc

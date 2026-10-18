import InitECandidate.Runtime.CostAnalyzerBase
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Structural bound search over straight code, counted loops, literal-size
mem* calls, allocations, shared stores and the given bounded callees. -/
syntax "vm_search" "[" term,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| vm_search [$fs,*]) => `(tactic| repeat first
      | exact ProgBounded.straight _ (by decide)
      $[| exact ProgBounded.call $fs _ _]*
      $[| exact ProgBounded.tail $fs _]*
      $[| apply ProgBounded.decCall $fs]*
      | exact CountedBody.incr
      | (apply CountedBody.seq; (case avoid => decide); (case noCont => decide);
          (case bounded => vm_search [$fs,*]); (case rest => vm_search [$fs,*]))
      | (apply ProgBounded.countedDec; (case hop => first | exact Or.inl rfl | exact Or.inr rfl);
          (case begin => decide); (case counted => vm_search [$fs,*]); (case rest => vm_search [$fs,*]);
          (case small => decide); (case positive => decide))
      | (apply ProgBounded.countedAssign; (case hop => first | exact Or.inl rfl | exact Or.inr rfl);
          (case begin => decide); (case counted => vm_search [$fs,*]); (case rest => vm_search [$fs,*]);
          (case small => decide); (case positive => decide))
      | exact ProgBounded.alloc _ _
      | exact memzero_const_progBounded _ _ (by decide)
      | exact memcpy_const_progBounded _ _ _ (by decide)
      | (apply memeq_decCall_const_progBounded; (case small => decide))
      | exact ProgBounded.sharedStore _ _ _
      | apply ProgBounded.seq
      | apply ProgBounded.iteMax
      | apply ProgBounded.dec)

/-- vm_search followed by discharge of the remaining literal side conditions. -/
syntax "vm_bound" "[" term,* "]" : tactic
macro_rules
  | `(tactic| vm_bound [$fs,*]) => `(tactic| (vm_search [$fs,*]); all_goals decide)

end InitECandidate.Runtime

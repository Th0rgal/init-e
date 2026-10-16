import InitECandidate.Runtime.WordWork

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Callee, normal-return and exception budgets at the actual source states.
An impossible or unreached continuation has budget zero. -/
noncomputable def callWorkBudgets {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width C F) : Nat × Nat × Nat :=
  match getVars args source with
  | none => (0, 0, 0)
  | some xs =>
      if wordSemBadDestArgs dest args then (0, 0, 0) else
      match wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize with
      | none => (0, 0, 0)
      | some (args1, prog, ss) =>
          match ret with
          | none =>
              match handler with
              | some _ => (0, 0, 0)
              | none => if source.clock = 0 then (0, 0, 0) else
                  (wordWork prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
                    (Flapjack.WordSemStateFiniteExact.decClock source)), 0, 0)
          | some (values, names, retCode, l1, l2) =>
              if sptDomainEmpty names.1 ∨ ¬ values.Nodup then (0, 0, 0) else
              match wordSemCutEnvs names source.locals with
              | none => (0, 0, 0)
              | some envs =>
                  if source.clock = 0 then (0, 0, 0) else
                  let entry := Flapjack.WordSemStateFiniteExact.callEnv args1 ss
                    (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock source))
                  let callee := wordWork prog entry
                  match fixClock entry (evaluate prog entry) with
                  | (some (.result location returned), middle) =>
                      (callee, if location ≠ .loc l1 l2 ∨ returned.length ≠ values.length then 0 else
                        match popEnv middle with
                        | none => 0
                        | some popped => if sptDomainEqUnion popped.locals envs.1 envs.2 then
                            wordWork retCode (Flapjack.WordSemStateFiniteExact.setVars values returned popped)
                          else 0, 0)
                  | (some (.exception location value), middle) =>
                      (callee, 0, match handler with
                        | none => 0
                        | some (reg, handlerCode, h1, h2) =>
                            if location ≠ .loc h1 h2 then 0 else
                            if sptDomainEqUnion middle.locals envs.1 envs.2 then
                              wordWork handlerCode (Flapjack.WordSemStateFiniteExact.setVar reg value middle)
                            else 0)
                  | _ => (callee, 0, 0)

/-- The total parent budget funds the conservative sum used by Call lowering. -/
theorem callWorkBudgets_funded {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width C F) :
    (callWorkBudgets ret dest args handler source).1 +
      (callWorkBudgets ret dest args handler source).2.1 +
      (callWorkBudgets ret dest args handler source).2.2 ≤
      wordWork (.call ret dest args handler) source := by
  rw [wordWork]
  unfold callWorkBudgets
  repeat' first | omega | (split <;> try simp_all)

#print axioms callWorkBudgets_funded
end InitECandidate.Runtime.WordToStack

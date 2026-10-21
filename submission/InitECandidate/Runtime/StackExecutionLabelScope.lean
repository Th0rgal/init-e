import InitECandidate.Runtime.StackExecutionTrace
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Labels introduced by this source subprogram are installed in its code map.
For a stored function this follows directly from the original locCheckExact,
without a separately computed certificate for every call site. -/
def ExecutionLabelScope (code : Spt (HolProg 64)) (p : HolProg 64) : Prop :=
  ∀ label, StackSem.getLabelsExact p label → StackSem.locCheckExact code label

theorem ExecutionLabelScope.of_lookup {code : Spt (HolProg 64)} {key : Nat} {p : HolProg 64}
    (lookup : sptLookup key code = some p) : ExecutionLabelScope code p := by
  intro label member
  exact Or.inr ⟨key, p, lookup, member⟩

theorem ExecutionLabelScope.entry {code : Spt (HolProg 64)} (dest : Nat ⊕ Nat) :
    ExecutionLabelScope code (.call none dest none) := by
  intro label member
  simpa only [StackSem.getLabelsExact] using member

theorem ExecutionLabelScope.seq_left {code : Spt (HolProg 64)} {first second : HolProg 64}
    (scope : ExecutionLabelScope code (.seq first second)) : ExecutionLabelScope code first :=
  fun label member => scope label (by simpa only [StackSem.getLabelsExact] using (Or.inl member))

theorem ExecutionLabelScope.seq_right {code : Spt (HolProg 64)} {first second : HolProg 64}
    (scope : ExecutionLabelScope code (.seq first second)) : ExecutionLabelScope code second :=
  fun label member => scope label (by simpa only [StackSem.getLabelsExact] using (Or.inr member))

theorem ExecutionLabelScope.ite_left {code : Spt (HolProg 64)} {yes no : HolProg 64}
    {cmp reg operand} (scope : ExecutionLabelScope code (.ite cmp reg operand yes no)) :
    ExecutionLabelScope code yes := fun label member => scope label (by simpa only [StackSem.getLabelsExact] using (Or.inl member))

theorem ExecutionLabelScope.ite_right {code : Spt (HolProg 64)} {yes no : HolProg 64}
    {cmp reg operand} (scope : ExecutionLabelScope code (.ite cmp reg operand yes no)) :
    ExecutionLabelScope code no := fun label member => scope label (by simpa only [StackSem.getLabelsExact] using (Or.inr member))

theorem ExecutionLabelScope.loop_body {code : Spt (HolProg 64)} {body : HolProg 64}
    (scope : ExecutionLabelScope code (.loop body)) : ExecutionLabelScope code body := by
  intro label member
  apply scope label
  simpa only [StackSem.getLabelsExact] using member

theorem ExecutionLabelScope.return_label {code : Spt (HolProg 64)} {rp : HolProg 64}
    {link l1 l2 dest handler}
    (scope : ExecutionLabelScope code (.call (some (rp, link, l1, l2)) dest handler)) :
    StackSem.locCheckExact code (l1, l2) := scope _ (by simp only [StackSem.getLabelsExact]; exact Or.inl True.intro)

theorem ExecutionLabelScope.return_body {code : Spt (HolProg 64)} {rp : HolProg 64}
    {link l1 l2 dest handler}
    (scope : ExecutionLabelScope code (.call (some (rp, link, l1, l2)) dest handler)) :
    ExecutionLabelScope code rp := fun label member => scope label (by simp only [StackSem.getLabelsExact]; exact Or.inr (Or.inl member))

theorem ExecutionLabelScope.handler_label {code : Spt (HolProg 64)} {rp hp : HolProg 64}
    {link l1 l2 dest hs hl}
    (scope : ExecutionLabelScope code (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl)))) :
    StackSem.locCheckExact code (hs, hl) := scope _ (by simp only [StackSem.getLabelsExact]; exact Or.inr (Or.inr (Or.inl True.intro)))

theorem ExecutionLabelScope.handler_body {code : Spt (HolProg 64)} {rp hp : HolProg 64}
    {link l1 l2 dest hs hl}
    (scope : ExecutionLabelScope code (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl)))) :
    ExecutionLabelScope code hp := fun label member => scope label (by simp only [StackSem.getLabelsExact]; exact Or.inr (Or.inr (Or.inr member)))

#print axioms ExecutionLabelScope.of_lookup
#print axioms ExecutionLabelScope.entry
#print axioms ExecutionLabelScope.seq_left
#print axioms ExecutionLabelScope.seq_right
#print axioms ExecutionLabelScope.ite_left
#print axioms ExecutionLabelScope.ite_right
#print axioms ExecutionLabelScope.loop_body
#print axioms ExecutionLabelScope.return_label
#print axioms ExecutionLabelScope.return_body
#print axioms ExecutionLabelScope.handler_label
#print axioms ExecutionLabelScope.handler_body
end InitECandidate.Runtime.StackToLab

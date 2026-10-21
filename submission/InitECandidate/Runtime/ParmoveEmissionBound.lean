import Flapjack.Compiler.Backend.Parmove
namespace InitECandidate.Runtime
open Flapjack.Compiler.Backend.Parmove

/-- Each un-emitted move owns two output slots, enough to break a cycle
through the temporary register. Searching dependencies consumes no slots. -/
def movePotential {α : Type} (state : State α) : Nat :=
  2 * (state.1.length + state.2.1.length) + state.2.2.length

theorem fstep_movePotential_le {α : Type} [DecidableEq α]
    (pending active emitted : List (Move α)) :
    movePotential (fstep (pending, active, emitted)) ≤ movePotential (pending, active, emitted) := by
  cases active with
  | nil =>
    cases pending with
    | nil => exact Nat.le_refl _
    | cons move pending =>
      rcases move with ⟨destination, source⟩
      simp only [fstep]
      split <;> simp [movePotential] <;> omega
  | cons move active =>
    rcases move with ⟨destination, source⟩
    have length := congrArg List.length (splitSource_append destination pending)
    simp only [List.length_append] at length
    simp only [fstep]
    cases suffix : (splitSource destination pending).2 with
    | cons next rest =>
      simp only [suffix, List.length_cons] at length
      simp [movePotential]
      omega
    | nil =>
      simp only
      cases active with
      | nil => simp [movePotential]; omega
      | cons head tail =>
        simp only
        split <;> simp [movePotential, frontLast_length] <;> omega

/-- The actual scheduler's output is linear, with no acyclicity or
well-formedness assumption on the original parallel move list. -/
theorem pmov_emitted_length_le {α : Type} [DecidableEq α] (state : State α) :
    (pmov state).2.2.length ≤ movePotential state := by
  rcases state with ⟨pending, active, emitted⟩
  rw [pmov]
  split
  · change emitted.length ≤ 2 * (pending.length + active.length) + emitted.length
    omega
  · rename_i unfinished
    have nonempty : pending ≠ [] ∨ active ≠ [] := by
      by_cases hp : pending = []
      · right
        intro ha
        exact unfinished ⟨hp, ha⟩
      · exact Or.inl hp
    have smaller := fstep_decreases pending active emitted nonempty
    exact Nat.le_trans (pmov_emitted_length_le (fstep (pending, active, emitted)))
      (fstep_movePotential_le pending active emitted)
termination_by measure state
decreasing_by exact smaller

theorem parmove_length_le {α : Type} [DecidableEq α] (moves : List (α × α)) :
    (parmove moves).length ≤ 2 * moves.length := by
  have bound := pmov_emitted_length_le
    (moves.map (fun move => (some move.1, some move.2)), [], [])
  simpa only [parmove, List.length_reverse, movePotential, List.length_map,
    List.length_nil, Nat.add_zero] using bound

#print axioms fstep_movePotential_le
#print axioms pmov_emitted_length_le
#print axioms parmove_length_le
end InitECandidate.Runtime

import Flapjack.Compiler.Backend.Parmove
namespace InitECandidate.Runtime.FineCost
open Flapjack.Compiler.Backend.Parmove

/-- Remaining moves have room for a cycle-saving temporary copy each. -/
def movePotential {α : Type} (state : State α) : Nat :=
  state.2.2.length + 2 * (state.1.length + state.2.1.length)

theorem move_step_potential {α : Type} [DecidableEq α]
    (pending active emitted : List (Move α)) :
    movePotential (fstep (pending, active, emitted)) ≤ movePotential (pending, active, emitted) := by
  cases active with
  | nil =>
    cases pending with
    | nil => simp [fstep, movePotential]
    | cons pair rest =>
      rcases pair with ⟨destination, source⟩
      simp only [fstep]
      split <;> simp [movePotential] <;> omega
  | cons pair active =>
    rcases pair with ⟨destination, source⟩
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

/-- The literal scheduler cannot emit more than its initial move potential. -/
theorem scheduler_potential {α : Type} [DecidableEq α] (state : State α) :
    movePotential (pmov state) ≤ movePotential state := by
  rw [pmov]
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans (scheduler_potential (fstep state))
      (by rcases state with ⟨pending, active, emitted⟩; exact move_step_potential pending active emitted)
termination_by measure state
decreasing_by
  rcases state with ⟨pending, active, emitted⟩
  apply fstep_decreases
  by_cases hp : pending = []
  · right
    intro ha
    simp_all
  · exact Or.inl hp

/-- At most two scheduled copies per input move, including all cycle saves. -/
theorem parallel_move_length {α : Type} [DecidableEq α] (moves : List (α × α)) :
    (parmove moves).length ≤ 2 * moves.length := by
  have bound := scheduler_potential
    (moves.map (fun move => (some move.1, some move.2)), [], [])
  unfold parmove
  rw [List.length_reverse]
  simp only [movePotential, List.length_map, List.length_nil, Nat.add_zero] at bound
  omega

#print axioms parallel_move_length
end InitECandidate.Runtime.FineCost

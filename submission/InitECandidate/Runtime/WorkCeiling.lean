import InitECandidate.Runtime.StackCodeSize
namespace InitECandidate.Runtime

/-- A clock decrement permits any procedure of bounded syntax size; within a
clock slice every syntactic subprogram strictly decreases the rank. -/
def workRank (limit fuel nodes : Nat) : Nat := fuel * (limit + 1) + nodes

def workCeiling (limit fuel nodes : Nat) : Nat := 8 ^ (workRank limit fuel nodes + 1)

theorem workRank_subprogram (limit oldFuel newFuel oldNodes newNodes : Nat)
    (clock : newFuel ≤ oldFuel) (nodesBound : newNodes < oldNodes) :
    workRank limit newFuel newNodes < workRank limit oldFuel oldNodes := by
  have scaled := Nat.mul_le_mul_right (limit + 1) clock
  unfold workRank
  omega

theorem workRank_clock (limit oldFuel newFuel oldNodes newNodes : Nat)
    (clock : newFuel < oldFuel) (nodesBound : newNodes ≤ limit) :
    workRank limit newFuel newNodes < workRank limit oldFuel oldNodes := by
  have step : newFuel + 1 ≤ oldFuel := by omega
  have scaled := Nat.mul_le_mul_right (limit + 1) step
  rw [Nat.add_mul, Nat.one_mul] at scaled
  unfold workRank
  omega

theorem workCeiling_child (limit oldFuel newFuel oldNodes newNodes : Nat)
    (smaller : workRank limit newFuel newNodes < workRank limit oldFuel oldNodes) :
    workCeiling limit newFuel newNodes ≤ 8 ^ workRank limit oldFuel oldNodes := by
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Three recursive branches with factor-two local composition fit into one
geometric rank step. Smaller fan-outs follow by setting unused budgets to zero. -/
theorem workCeiling_three (rank first second third : Nat)
    (one : first ≤ 8 ^ rank) (two : second ≤ 8 ^ rank) (three : third ≤ 8 ^ rank) :
    2 * (first + second + third) + 2 ≤ 8 ^ (rank + 1) := by
  have positive : 0 < 8 ^ rank := Nat.pow_pos (by decide)
  rw [Nat.pow_succ]
  omega

theorem workCeiling_two (rank first second : Nat)
    (one : first ≤ 8 ^ rank) (two : second ≤ 8 ^ rank) :
    2 + first + second ≤ 8 ^ (rank + 1) := by
  have combined := workCeiling_three rank first second 0 one two (Nat.zero_le _)
  omega

theorem workCeiling_one (rank first : Nat) (one : first ≤ 8 ^ rank) :
    2 + first ≤ 8 ^ (rank + 1) := by
  have combined := workCeiling_two rank first 0 one (Nat.zero_le _)
  omega

theorem two_le_workCeiling (limit fuel nodes : Nat) : 2 ≤ workCeiling limit fuel nodes := by
  have combined := workCeiling_one (workRank limit fuel nodes) 0 (Nat.zero_le _)
  exact combined

#print axioms workRank_clock
#print axioms workCeiling_three
end InitECandidate.Runtime

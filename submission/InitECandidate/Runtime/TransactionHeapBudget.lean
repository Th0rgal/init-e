import InitECandidate.Runtime.VersionedHashesSourceStepHeapGrowth
namespace InitECandidate.Runtime

/-- A uniform upper bound on a successful transaction decoders allocation growth. -/
def transactionHeapGrowth (length : Nat) : Nat :=
  400 + length * 56 + (length * 48 + 46) * length + length * 280

/-- Persistent growth plus scratch space needed to decode the next transaction. -/
def transactionHeapWorkspace (length : Nat) : Nat :=
  transactionHeapGrowth length + length * 16 + 14

theorem transaction_heap_growth_mono (left right : Nat) (bounded : left ≤ right) :
    transactionHeapGrowth left ≤ transactionHeapGrowth right := by
  have linear := Nat.mul_le_mul_right 56 bounded
  have tail := Nat.mul_le_mul_right 280 bounded
  have factor : left * 48 + 46 ≤ right * 48 + 46 := by omega
  have quadratic := Nat.mul_le_mul factor bounded
  dsimp only [transactionHeapGrowth]
  omega

theorem transaction_heap_workspace_mono (left right : Nat) (bounded : left ≤ right) :
    transactionHeapWorkspace left ≤ transactionHeapWorkspace right := by
  have growth := transaction_heap_growth_mono left right bounded
  have scratch := Nat.mul_le_mul_right 16 bounded
  dsimp only [transactionHeapWorkspace]
  omega

theorem transaction_heap_workspace_exact (length : Nat) :
    transactionHeapWorkspace length =
      400 + length * 56 + (length * 48 + 46) * length + length * 296 + 14 := by
  dsimp only [transactionHeapWorkspace,transactionHeapGrowth]
  omega

/-- One successful iteration consumes at most one growth allowance, leaving
all remaining allowances and the next decoders workspace available. -/
theorem transaction_heap_reserve_step (heap next remaining length frame : Nat)
    (active : 0 < remaining)
    (growth : next ≤ heap + transactionHeapGrowth length)
    (reserve : heap + remaining * transactionHeapGrowth length + transactionHeapWorkspace length ≤ frame) :
    next + (remaining - 1) * transactionHeapGrowth length + transactionHeapWorkspace length ≤ frame := by
  have split : remaining = (remaining - 1) + 1 := by omega
  have product : remaining * transactionHeapGrowth length =
      (remaining - 1) * transactionHeapGrowth length + transactionHeapGrowth length := by
    calc
      remaining * transactionHeapGrowth length = ((remaining - 1) + 1) * transactionHeapGrowth length :=
        congrArg (fun n => n * transactionHeapGrowth length) split
      _ = _ := by rw [Nat.add_mul,Nat.one_mul]
  omega

#print axioms transaction_heap_growth_mono
#print axioms transaction_heap_workspace_mono
#print axioms transaction_heap_workspace_exact
#print axioms transaction_heap_reserve_step
end InitECandidate.Runtime

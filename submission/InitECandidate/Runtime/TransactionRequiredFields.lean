import InitECandidate.Runtime.TransactionIndexScopeKindBound
namespace InitECandidate.Runtime

/-- Fields consumed from decoder initialization through the final signature. -/
def transactionRequiredFields (kind : BitVec 64) : Nat :=
  (if kind = 0#64 then (0 : BitVec 64) else 1).toNat +
  (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) +
  (if kind = 4#64 then 1 else 0) + (if 1#64 < kind then 10 else 9)

/-- The refined proof margins match the original source's field counts for
legacy and transaction types 1 through 4. -/
theorem transaction_required_fields_table :
    ([0,1,2,3,4] : List (BitVec 64)).map transactionRequiredFields = [9,11,12,14,13] := by
  decide

#print axioms transaction_required_fields_table
end InitECandidate.Runtime

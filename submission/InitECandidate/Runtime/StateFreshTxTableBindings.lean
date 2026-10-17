import InitECandidate.Runtime.StateFreshTxConcretePlan
namespace InitECandidate.Runtime
open Flapjack

/-- Transaction-state field offsets paired with the exact table addresses
produced by the original constructor order. -/
def stateFreshTxTableBindings (pointer : BitVec 64) : List (Nat × Nat × Nat) → List (Nat × BitVec 64)
  | [] => []
  | (width,capacity,offset) :: rest =>
    (offset,pointer) :: stateFreshTxTableBindings (stateFreshTxNextTable pointer width capacity) rest

/-- Constructors retain every previously registered table identity. -/
theorem stateFreshTx_registry_contains_initial (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64) (tables : Set (BitVec 64)), tables ⊆ stateFreshTxRegistryAfter pointer specs tables := by
  induction specs with
  | nil => intro pointer tables table member; exact member
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro pointer tables table member
      exact ih (stateFreshTxNextTable pointer width capacity) (insert pointer tables) (Set.mem_insert_of_mem pointer member)

/-- Every transaction field binding names a table in the final registry. -/
theorem stateFreshTx_binding_registered (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64) (tables : Set (BitVec 64)) (binding : Nat × BitVec 64),
      binding ∈ stateFreshTxTableBindings pointer specs → binding.2 ∈ stateFreshTxRegistryAfter pointer specs tables := by
  induction specs with
  | nil => intro pointer tables binding member; cases member
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro pointer tables binding member
      rcases List.mem_cons.mp member with same | later
      · subst binding
        exact stateFreshTx_registry_contains_initial rest (stateFreshTxNextTable pointer width capacity) (insert pointer tables) (Set.mem_insert pointer tables)
      · exact ih (stateFreshTxNextTable pointer width capacity) (insert pointer tables) binding later

/-- The eight actual table fields exhaust the transaction header after parent. -/
theorem stateFreshTx_table_binding_offsets (pointer : BitVec 64) :
    (stateFreshTxTableBindings pointer stateFreshTxAllTables).map Prod.fst = [8,16,24,32,40,48,56,64] := by rfl

#print axioms stateFreshTx_registry_contains_initial
#print axioms stateFreshTx_binding_registered
#print axioms stateFreshTx_table_binding_offsets
end InitECandidate.Runtime

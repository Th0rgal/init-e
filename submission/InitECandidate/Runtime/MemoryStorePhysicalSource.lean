import InitECandidate.Runtime.EvmMstore8Source
import InitECandidate.Runtime.EvmMstoreSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Exactly the two original stores sharing the checked-pop/charge prefix. -/
inductive MemoryStorePhysicalKind | byte | word

def memoryStorePhysicalWidth : MemoryStorePhysicalKind→BitVec 64
 | .byte=>1
 | .word=>32

def memoryStorePhysicalAt (kind : MemoryStorePhysicalKind) (index : Nat) : ProgHOL 64 :=
 match kind with
 | .byte=>mstore8At index
 | .word=>mstoreAt index

def memoryStorePhysicalBody : MemoryStorePhysicalKind→ProgHOL 64
 | .byte=>sourceFunctionBody Guest.guestFn_op_mstore8
 | .word=>sourceFunctionBody Guest.guestFn_op_mstore

theorem source_memory_store_physical_body (kind : MemoryStorePhysicalKind) :
 memoryStorePhysicalBody kind=memoryStorePhysicalAt kind 0 := by
 cases kind <;>simp only [memoryStorePhysicalBody,memoryStorePhysicalAt,sourceFunctionBody_eq_structural] <;>rfl

theorem source_memory_store_physical_0 (kind : MemoryStorePhysicalKind) :
 memoryStorePhysicalAt kind 0=.decCall (ofString "start") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (memoryStorePhysicalAt kind 1) := by cases kind <;>rfl

theorem source_memory_store_physical_1 (kind : MemoryStorePhysicalKind) :
 memoryStorePhysicalAt kind 1=.decCall (ofString "value") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (memoryStorePhysicalAt kind 2) := by cases kind <;>rfl

theorem source_memory_store_physical_2 (kind : MemoryStorePhysicalKind) :
 memoryStorePhysicalAt kind 2=.seq (.call (some (none,none)) (ofString "charge_with_memory") [.const 3,.var .local (ofString "start"),.rstruct [.const (memoryStorePhysicalWidth kind),.const 0,.const 0,.const 0]]) (memoryStorePhysicalAt kind 3) := by cases kind <;>rfl
#print axioms source_memory_store_physical_body
#print axioms source_memory_store_physical_0
#print axioms source_memory_store_physical_1
#print axioms source_memory_store_physical_2
end InitECandidate.Runtime

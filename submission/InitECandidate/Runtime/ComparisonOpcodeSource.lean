import InitECandidate.Runtime.BitwiseOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite comparison opcodes: two real pops, literal charge, a
checked one-word helper result, then the boolean push and PC/return. -/
inductive ComparisonOpcodeKind | lt | gt | eq

def comparisonOpcodeName : ComparisonOpcodeKind→MlS
 | .lt=>ofString "op_lt"
 | .gt=>ofString "op_gt"
 | .eq=>ofString "op_eq"

def comparisonOpcodeHelper : ComparisonOpcodeKind→MlS
 | .lt=>ofString "u256_lt"
 | .gt=>ofString "u256_gt"
 | .eq=>ofString "u256_eq"

def comparisonOpcodeBody : ComparisonOpcodeKind→ProgHOL 64
 | .lt=>sourceFunctionBody Guest.guestFn_op_lt
 | .gt=>sourceFunctionBody Guest.guestFn_op_gt
 | .eq=>sourceFunctionBody Guest.guestFn_op_eq

def comparisonOpcodeAt (kind : ComparisonOpcodeKind) (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody (match kind with
  | .lt=>Guest.guestFn_op_lt
  | .gt=>Guest.guestFn_op_gt
  | .eq=>Guest.guestFn_op_eq))

def comparisonOpcodeFee : ComparisonOpcodeKind→BitVec 64 :=fun _=>3

def comparisonOpcodeSourceCost (kind : ComparisonOpcodeKind) : Nat:=1+(1+(1+(1+2)))

theorem source_comparison_opcode_body (kind : ComparisonOpcodeKind) : comparisonOpcodeBody kind=comparisonOpcodeAt kind 0 := by
 cases kind <;>(simp only [comparisonOpcodeBody,comparisonOpcodeAt,sourceFunctionBody_eq_structural];rfl)

theorem source_comparison_opcode_0 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (comparisonOpcodeAt kind 1) := by cases kind <;>rfl

theorem source_comparison_opcode_1 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 1=.decCall (ofString "y") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (comparisonOpcodeAt kind 2) := by cases kind <;>rfl

theorem source_comparison_opcode_2 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const (comparisonOpcodeFee kind)]) (comparisonOpcodeAt kind 3) := by cases kind <;>rfl

theorem source_comparison_opcode_3 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 3=.decCall (ofString "r") .one (comparisonOpcodeHelper kind) [.var .local (ofString "x"),.var .local (ofString "y")] (comparisonOpcodeAt kind 4) := by cases kind <;>rfl

theorem source_comparison_opcode_4 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 4=.seq (.call (some (none,none)) (ofString "stack_push_bool") [.var .local (ofString "r")]) (comparisonOpcodeAt kind 5) := by cases kind <;>rfl

theorem source_comparison_opcode_5 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (comparisonOpcodeAt kind 6) := by cases kind <;>rfl

theorem source_comparison_opcode_6 (kind : ComparisonOpcodeKind) : comparisonOpcodeAt kind 6=.return (.const 0) := by cases kind <;>rfl
#print axioms source_comparison_opcode_body
#print axioms source_comparison_opcode_3
#print axioms source_comparison_opcode_6

/-- The direct finite `op_iszero`: one real pop, literal charge, checked
one-word helper result, boolean push and PC/return. -/
def zeroOpcodeBody : ProgHOL 64:=sourceFunctionBody Guest.guestFn_op_iszero

def zeroOpcodeAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_iszero)

def zeroOpcodeName : MlS:=ofString "op_iszero"

def zeroOpcodeHelper : MlS:=ofString "u256_is_zero"

def zeroOpcodeFee : BitVec 64:=3

def zeroOpcodeSourceCost : Nat:=1+(1+(1+2))

theorem source_zero_opcode_body : zeroOpcodeBody=zeroOpcodeAt 0 := by
 simp only [zeroOpcodeBody,sourceFunctionBody_eq_structural];rfl

theorem source_zero_opcode_0 : zeroOpcodeAt 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (zeroOpcodeAt 1) := by rfl

theorem source_zero_opcode_1 : zeroOpcodeAt 1=.seq (.call (some (none,none)) (ofString "charge_gas") [.const zeroOpcodeFee]) (zeroOpcodeAt 2) := by rfl

theorem source_zero_opcode_2 : zeroOpcodeAt 2=.decCall (ofString "r") .one zeroOpcodeHelper [.var .local (ofString "x")] (zeroOpcodeAt 3) := by rfl

theorem source_zero_opcode_3 : zeroOpcodeAt 3=.seq (.call (some (none,none)) (ofString "stack_push_bool") [.var .local (ofString "r")]) (zeroOpcodeAt 4) := by rfl

theorem source_zero_opcode_4 : zeroOpcodeAt 4=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (zeroOpcodeAt 5) := by rfl

theorem source_zero_opcode_5 : zeroOpcodeAt 5=.return (.const 0) := by rfl
#print axioms source_zero_opcode_body
#print axioms source_zero_opcode_2
end InitECandidate.Runtime

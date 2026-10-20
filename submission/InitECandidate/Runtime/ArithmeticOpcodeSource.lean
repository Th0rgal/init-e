import InitECandidate.Runtime.EvmMstoreSource
import InitECandidate.Runtime.VmFn_u256_add
import InitECandidate.Runtime.VmFn_u256_sub
import InitECandidate.Runtime.VmFn_u256_mul
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
inductive ArithmeticOpcodeKind | add | sub | mul

def arithmeticOpcodeBody : ArithmeticOpcodeKind→ProgHOL 64
 | .add=>sourceFunctionBody Guest.guestFn_op_add
 | .sub=>sourceFunctionBody Guest.guestFn_op_sub
 | .mul=>sourceFunctionBody Guest.guestFn_op_mul

def arithmeticOpcodeAt (kind : ArithmeticOpcodeKind) (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (match kind with
 | .add=>structuralFunctionBody Guest.guestFn_op_add
 | .sub=>structuralFunctionBody Guest.guestFn_op_sub
 | .mul=>structuralFunctionBody Guest.guestFn_op_mul)

def arithmeticOpcodeHelper : ArithmeticOpcodeKind→MlS
 | .add=>ofString "u256_add"
 | .sub=>ofString "u256_sub"
 | .mul=>ofString "u256_mul"

def arithmeticOpcodeFee : ArithmeticOpcodeKind→BitVec 64
 | .add|.sub=>3
 | .mul=>5

def arithmeticOpcodeHelperCost : ArithmeticOpcodeKind→Nat
 | .add|.sub=>0
 | .mul=>7

theorem arithmetic_opcode_helper_bounded (kind : ArithmeticOpcodeKind) : FunBounded (arithmeticOpcodeHelper kind) (arithmeticOpcodeHelperCost kind) := by
 cases kind with
 | add=>exact vmBound_u256_add
 | sub=>exact vmBound_u256_sub
 | mul=>exact vmBound_u256_mul

theorem source_arithmetic_opcode_body (kind : ArithmeticOpcodeKind) : arithmeticOpcodeBody kind=arithmeticOpcodeAt kind 0 := by cases kind <;>simp only [arithmeticOpcodeBody,sourceFunctionBody_eq_structural] <;>rfl

theorem source_arithmetic_opcode_0 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (arithmeticOpcodeAt kind 1) := by cases kind <;>rfl

theorem source_arithmetic_opcode_1 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 1=.decCall (ofString "y") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (arithmeticOpcodeAt kind 2) := by cases kind <;>rfl

theorem source_arithmetic_opcode_2 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const (arithmeticOpcodeFee kind)]) (arithmeticOpcodeAt kind 3) := by cases kind <;>rfl

theorem source_arithmetic_opcode_3 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 3=.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (arithmeticOpcodeHelper kind) [.var .local (ofString "x"),.var .local (ofString "y")] (arithmeticOpcodeAt kind 4) := by cases kind <;>rfl

theorem source_arithmetic_opcode_4 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 4=.seq (.call (some (none,none)) (ofString "stack_push") [.var .local (ofString "r")]) (arithmeticOpcodeAt kind 5) := by cases kind <;>rfl

theorem source_arithmetic_opcode_5 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (arithmeticOpcodeAt kind 6) := by cases kind <;>rfl

theorem source_arithmetic_opcode_6 (kind : ArithmeticOpcodeKind) : arithmeticOpcodeAt kind 6=.return (.const 0) := by cases kind <;>rfl
#print axioms arithmetic_opcode_helper_bounded
#print axioms source_arithmetic_opcode_body
#print axioms source_arithmetic_opcode_0
#print axioms source_arithmetic_opcode_1
#print axioms source_arithmetic_opcode_2
#print axioms source_arithmetic_opcode_3
#print axioms source_arithmetic_opcode_4
#print axioms source_arithmetic_opcode_5
#print axioms source_arithmetic_opcode_6
end InitECandidate.Runtime

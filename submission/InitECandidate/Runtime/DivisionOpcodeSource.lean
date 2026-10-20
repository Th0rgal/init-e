import InitECandidate.Runtime.BitwiseOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite division opcodes: two real pops, literal charge, a
checked four-limb helper result, then the struct push and PC/return. -/
inductive DivisionOpcodeKind | div | sdiv | mod | smod

def divisionOpcodeName : DivisionOpcodeKind→MlS
 | .div=>ofString "op_div"
 | .sdiv=>ofString "op_sdiv"
 | .mod=>ofString "op_mod"
 | .smod=>ofString "op_smod"

def divisionOpcodeHelper : DivisionOpcodeKind→MlS
 | .div=>ofString "u256_div"
 | .sdiv=>ofString "u256_sdiv"
 | .mod=>ofString "u256_mod"
 | .smod=>ofString "u256_smod"

def divisionOpcodeBody : DivisionOpcodeKind→ProgHOL 64
 | .div=>sourceFunctionBody Guest.guestFn_op_div
 | .sdiv=>sourceFunctionBody Guest.guestFn_op_sdiv
 | .mod=>sourceFunctionBody Guest.guestFn_op_mod
 | .smod=>sourceFunctionBody Guest.guestFn_op_smod

def divisionOpcodeAt (kind : DivisionOpcodeKind) (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody (match kind with
  | .div=>Guest.guestFn_op_div
  | .sdiv=>Guest.guestFn_op_sdiv
  | .mod=>Guest.guestFn_op_mod
  | .smod=>Guest.guestFn_op_smod))

def divisionOpcodeFee : DivisionOpcodeKind→BitVec 64 :=fun _=>5

def divisionOpcodeSourceCost (kind : DivisionOpcodeKind) : Nat:=1+(1+(1+(1+2)))

theorem source_division_opcode_body (kind : DivisionOpcodeKind) : divisionOpcodeBody kind=divisionOpcodeAt kind 0 := by
 cases kind <;>(simp only [divisionOpcodeBody,divisionOpcodeAt,sourceFunctionBody_eq_structural];rfl)

theorem source_division_opcode_0 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (divisionOpcodeAt kind 1) := by cases kind <;>rfl

theorem source_division_opcode_1 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 1=.decCall (ofString "y") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (divisionOpcodeAt kind 2) := by cases kind <;>rfl

theorem source_division_opcode_2 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const (divisionOpcodeFee kind)]) (divisionOpcodeAt kind 3) := by cases kind <;>rfl

theorem source_division_opcode_3 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 3=.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (divisionOpcodeHelper kind) [.var .local (ofString "x"),.var .local (ofString "y")] (divisionOpcodeAt kind 4) := by cases kind <;>rfl

theorem source_division_opcode_4 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 4=.seq (.call (some (none,none)) (ofString "stack_push") [.var .local (ofString "r")]) (divisionOpcodeAt kind 5) := by cases kind <;>rfl

theorem source_division_opcode_5 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (divisionOpcodeAt kind 6) := by cases kind <;>rfl

theorem source_division_opcode_6 (kind : DivisionOpcodeKind) : divisionOpcodeAt kind 6=.return (.const 0) := by cases kind <;>rfl
#print axioms source_division_opcode_body
#print axioms source_division_opcode_3
#print axioms source_division_opcode_6


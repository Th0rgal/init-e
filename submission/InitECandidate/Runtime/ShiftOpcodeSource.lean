import InitECandidate.Runtime.BitwiseOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite shift opcodes: two real pops, literal charge, the
`saturating` shift-amount helper returning one word, a checked four-limb result
and then the struct push and PC/return. -/
inductive ShiftOpcodeKind | shl | shr | sar

def shiftOpcodeName : ShiftOpcodeKind→MlS
 | .shl=>ofString "op_shl"
 | .shr=>ofString "op_shr"
 | .sar=>ofString "op_sar"

def shiftOpcodeHelper : ShiftOpcodeKind→MlS
 | .shl=>ofString "u256_shl"
 | .shr=>ofString "u256_shr"
 | .sar=>ofString "u256_sar"

def shiftOpcodeBody : ShiftOpcodeKind→ProgHOL 64
 | .shl=>sourceFunctionBody Guest.guestFn_op_shl
 | .shr=>sourceFunctionBody Guest.guestFn_op_shr
 | .sar=>sourceFunctionBody Guest.guestFn_op_sar

def shiftOpcodeAt (kind : ShiftOpcodeKind) (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody (match kind with
  | .shl=>Guest.guestFn_op_shl
  | .shr=>Guest.guestFn_op_shr
  | .sar=>Guest.guestFn_op_sar))

def shiftOpcodeFee : ShiftOpcodeKind→BitVec 64 :=fun _=>3

def shiftOpcodeSourceCost (kind : ShiftOpcodeKind) : Nat:=1+(1+(1+(1+(1+2))))

theorem source_shift_opcode_body (kind : ShiftOpcodeKind) : shiftOpcodeBody kind=shiftOpcodeAt kind 0 := by
 cases kind <;>(simp only [shiftOpcodeBody,shiftOpcodeAt,sourceFunctionBody_eq_structural];rfl)

theorem source_shift_opcode_0 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 0=.decCall (ofString "sh") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (shiftOpcodeAt kind 1) := by cases kind <;>rfl
theorem source_shift_opcode_1 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 1=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (shiftOpcodeAt kind 2) := by cases kind <;>rfl
theorem source_shift_opcode_2 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const (shiftOpcodeFee kind)]) (shiftOpcodeAt kind 3) := by cases kind <;>rfl
theorem source_shift_opcode_3 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 3=.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "sh")] (shiftOpcodeAt kind 4) := by cases kind <;>rfl
theorem source_shift_opcode_4 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 4=.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (shiftOpcodeHelper kind) [.var .local (ofString "x"),.var .local (ofString "n")] (shiftOpcodeAt kind 5) := by cases kind <;>rfl
theorem source_shift_opcode_5 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 5=.seq (.call (some (none,none)) (ofString "stack_push") [.var .local (ofString "r")]) (shiftOpcodeAt kind 6) := by cases kind <;>rfl
theorem source_shift_opcode_6 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 6=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (shiftOpcodeAt kind 7) := by cases kind <;>rfl
theorem source_shift_opcode_7 (kind : ShiftOpcodeKind) : shiftOpcodeAt kind 7=.return (.const 0) := by cases kind <;>rfl
#print axioms source_shift_opcode_body
#print axioms source_shift_opcode_0
#print axioms source_shift_opcode_1
#print axioms source_shift_opcode_2
#print axioms source_shift_opcode_3
#print axioms source_shift_opcode_4
#print axioms source_shift_opcode_5
#print axioms source_shift_opcode_6
#print axioms source_shift_opcode_7
end InitECandidate.Runtime

import InitECandidate.Runtime.ArithmeticOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite bitwise opcode family: no helper declaration, the real
source pushes the four-limb struct expression evaluated in place. -/
inductive BitwiseBinaryKind | and | or | xor

def bitwiseOpcodeBody : BitwiseBinaryKind→ProgHOL 64
 | .and=>sourceFunctionBody Guest.guestFn_op_and
 | .or=>sourceFunctionBody Guest.guestFn_op_or
 | .xor=>sourceFunctionBody Guest.guestFn_op_xor

def bitwiseOpcodeAt (kind : BitwiseBinaryKind) (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (match kind with
 | .and=>structuralFunctionBody Guest.guestFn_op_and
 | .or=>structuralFunctionBody Guest.guestFn_op_or
 | .xor=>structuralFunctionBody Guest.guestFn_op_xor)

def bitwiseOpcodeName : BitwiseBinaryKind→MlS
 | .and=>ofString "op_and"
 | .or=>ofString "op_or"
 | .xor=>ofString "op_xor"

def bitwiseOpcodeFee : BitwiseBinaryKind→BitVec 64
 | _=>3

/-- Exact prefix-sum form, matching the source shape pop/pop/charge/push/pc/return. -/
def bitwiseOpcodeSourceCost (kind : BitwiseBinaryKind) : Nat:=1+(1+(1+(1+2)))

theorem source_bitwise_opcode_body (kind : BitwiseBinaryKind) : bitwiseOpcodeBody kind=bitwiseOpcodeAt kind 0 := by
 cases kind <;>simp only [bitwiseOpcodeBody,sourceFunctionBody_eq_structural] <;>rfl

theorem source_bitwise_opcode_0 (kind : BitwiseBinaryKind) : bitwiseOpcodeAt kind 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (bitwiseOpcodeAt kind 1) := by cases kind <;>rfl

theorem source_bitwise_opcode_1 (kind : BitwiseBinaryKind) : bitwiseOpcodeAt kind 1=.decCall (ofString "y") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (bitwiseOpcodeAt kind 2) := by cases kind <;>rfl

theorem source_bitwise_opcode_2 (kind : BitwiseBinaryKind) : bitwiseOpcodeAt kind 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const (bitwiseOpcodeFee kind)]) (bitwiseOpcodeAt kind 3) := by cases kind <;>rfl

/-- The real direct source push argument: four limbs combined by the matching
bitwise BinOp, no helper call. -/
def bitwisePushValue (kind : BitwiseBinaryKind) : ExpHOL 64 :=
 match kind with
 | .and=>.rstruct [.op BinOp.and [.rfield 0 (.var .local (ofString "x")),.rfield 0 (.var .local (ofString "y"))],.op BinOp.and [.rfield 1 (.var .local (ofString "x")),.rfield 1 (.var .local (ofString "y"))],.op BinOp.and [.rfield 2 (.var .local (ofString "x")),.rfield 2 (.var .local (ofString "y"))],.op BinOp.and [.rfield 3 (.var .local (ofString "x")),.rfield 3 (.var .local (ofString "y"))]]
 | .or=>.rstruct [.op BinOp.or [.rfield 0 (.var .local (ofString "x")),.rfield 0 (.var .local (ofString "y"))],.op BinOp.or [.rfield 1 (.var .local (ofString "x")),.rfield 1 (.var .local (ofString "y"))],.op BinOp.or [.rfield 2 (.var .local (ofString "x")),.rfield 2 (.var .local (ofString "y"))],.op BinOp.or [.rfield 3 (.var .local (ofString "x")),.rfield 3 (.var .local (ofString "y"))]]
 | .xor=>.rstruct [.op BinOp.xor [.rfield 0 (.var .local (ofString "x")),.rfield 0 (.var .local (ofString "y"))],.op BinOp.xor [.rfield 1 (.var .local (ofString "x")),.rfield 1 (.var .local (ofString "y"))],.op BinOp.xor [.rfield 2 (.var .local (ofString "x")),.rfield 2 (.var .local (ofString "y"))],.op BinOp.xor [.rfield 3 (.var .local (ofString "x")),.rfield 3 (.var .local (ofString "y"))]]

theorem source_bitwise_opcode_3 (kind : BitwiseBinaryKind) :
 bitwiseOpcodeAt kind 3=.seq (.call (some (none,none)) (ofString "stack_push") [bitwisePushValue kind]) (bitwiseOpcodeAt kind 4) := by cases kind <;>rfl

theorem source_bitwise_opcode_4 (kind : BitwiseBinaryKind) : bitwiseOpcodeAt kind 4=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (bitwiseOpcodeAt kind 5) := by cases kind <;>rfl

theorem source_bitwise_opcode_5 (kind : BitwiseBinaryKind) : bitwiseOpcodeAt kind 5=.return (.const 0) := by cases kind <;>rfl
#print axioms source_bitwise_opcode_body
#print axioms source_bitwise_opcode_0
#print axioms source_bitwise_opcode_1
#print axioms source_bitwise_opcode_2
#print axioms source_bitwise_opcode_3
#print axioms source_bitwise_opcode_4
#print axioms source_bitwise_opcode_5
end InitECandidate.Runtime

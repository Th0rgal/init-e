import InitECandidate.Runtime.BitwiseOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite NOT opcode: one real pop, literal charge, the real
four-limb complement struct push (xor with all-ones), and PC/return. -/
def notOpcodeBody : ProgHOL 64:=sourceFunctionBody Guest.guestFn_op_not

def notOpcodeAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_not)

def notOpcodeName : MlS:=ofString "op_not"

def notOpcodeFee : BitVec 64:=3

def notOpcodeSourceCost : Nat:=1+(1+(1+2))

def notPushValue : ExpHOL 64:=.rstruct [.op BinOp.xor [.rfield 0 (.var .local (ofString "x")),.const 18446744073709551615],.op BinOp.xor [.rfield 1 (.var .local (ofString "x")),.const 18446744073709551615],.op BinOp.xor [.rfield 2 (.var .local (ofString "x")),.const 18446744073709551615],.op BinOp.xor [.rfield 3 (.var .local (ofString "x")),.const 18446744073709551615]]

theorem source_not_opcode_body : notOpcodeBody=notOpcodeAt 0 := by
 simp only [notOpcodeBody,sourceFunctionBody_eq_structural];rfl

theorem source_not_opcode_0 : notOpcodeAt 0=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (notOpcodeAt 1) := by rfl

theorem source_not_opcode_1 : notOpcodeAt 1=.seq (.call (some (none,none)) (ofString "charge_gas") [.const notOpcodeFee]) (notOpcodeAt 2) := by rfl

theorem source_not_opcode_2 : notOpcodeAt 2=.seq (.call (some (none,none)) (ofString "stack_push") [notPushValue]) (notOpcodeAt 3) := by rfl

theorem source_not_opcode_3 : notOpcodeAt 3=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (notOpcodeAt 4) := by rfl

theorem source_not_opcode_4 : notOpcodeAt 4=.return (.const 0) := by rfl
#print axioms source_not_opcode_body
#print axioms source_not_opcode_0
#print axioms source_not_opcode_2
end InitECandidate.Runtime

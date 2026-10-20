import InitECandidate.Runtime.ShiftOpcodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The direct finite sign-extension opcode: two real pops, literal charge 5,
the checked `sat_word` byte-width helper, the checked `u256_signextend` helper
and then the struct push and PC/return. -/
def signextendOpcodeName : MlS := ofString "op_signextend"

def signextendOpcodeBody : ProgHOL 64 := sourceFunctionBody Guest.guestFn_op_signextend

def signextendOpcodeAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_signextend)

def signextendOpcodeFee : BitVec 64 := 5

def signextendOpcodeSourceCost : Nat := 1+(1+(1+(1+(1+2))))

theorem source_signextend_opcode_body : signextendOpcodeBody=signextendOpcodeAt 0 := by
 simp only [signextendOpcodeBody,signextendOpcodeAt,sourceFunctionBody_eq_structural];rfl

theorem source_signextend_opcode_0 : signextendOpcodeAt 0=.decCall (ofString "b") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (signextendOpcodeAt 1) := by rfl
theorem source_signextend_opcode_1 : signextendOpcodeAt 1=.decCall (ofString "x") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (signextendOpcodeAt 2) := by rfl
theorem source_signextend_opcode_2 : signextendOpcodeAt 2=.seq (.call (some (none,none)) (ofString "charge_gas") [.const signextendOpcodeFee]) (signextendOpcodeAt 3) := by rfl
theorem source_signextend_opcode_3 : signextendOpcodeAt 3=.decCall (ofString "bw") .one (ofString "sat_word") [.var .local (ofString "b")] (signextendOpcodeAt 4) := by rfl
theorem source_signextend_opcode_4 : signextendOpcodeAt 4=.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "u256_signextend") [.var .local (ofString "bw"),.var .local (ofString "x")] (signextendOpcodeAt 5) := by rfl
theorem source_signextend_opcode_5 : signextendOpcodeAt 5=.seq (.call (some (none,none)) (ofString "stack_push") [.var .local (ofString "r")]) (signextendOpcodeAt 6) := by rfl
theorem source_signextend_opcode_6 : signextendOpcodeAt 6=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (signextendOpcodeAt 7) := by rfl
theorem source_signextend_opcode_7 : signextendOpcodeAt 7=.return (.const 0) := by rfl
#print axioms source_signextend_opcode_body
#print axioms source_signextend_opcode_0
#print axioms source_signextend_opcode_1
#print axioms source_signextend_opcode_2
#print axioms source_signextend_opcode_3
#print axioms source_signextend_opcode_4
#print axioms source_signextend_opcode_5
#print axioms source_signextend_opcode_6
#print axioms source_signextend_opcode_7
end InitECandidate.Runtime

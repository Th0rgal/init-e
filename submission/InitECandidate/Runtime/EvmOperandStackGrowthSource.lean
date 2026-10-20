import InitECandidate.Runtime.EvmOperandStackSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stackPushGrowthAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (match stackPushAt 2 with | .seq (.ite _ branch _) _=>branch | _=>.skip)

theorem source_stack_push_growth_0 : stackPushGrowthAt 0=.seq
 (.ite (.cmp .notLower (.var .local (ofString "cap")) (.const 1024)) (.raise (ofString "EvmErr") (.const 3)) .skip) (stackPushGrowthAt 1):=rfl
theorem source_stack_push_growth_1 : stackPushGrowthAt 1=.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"),.const 2]) (stackPushGrowthAt 2):=rfl
theorem source_stack_push_growth_2 : stackPushGrowthAt 2=.seq
 (.ite (.cmp .lower (.const 1024) (.var .local (ofString "ncap"))) (.assign .local (ofString "ncap") (.const 1024)) .skip) (stackPushGrowthAt 3):=rfl
theorem source_stack_push_growth_3 : stackPushGrowthAt 3=.decCall (ofString "ns") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "ncap"),.const 32]] (stackPushGrowthAt 4):=rfl
theorem source_stack_push_growth_4 : stackPushGrowthAt 4=.seq (.call (some (none,none)) (ofString "memcpy")
 [.var .local (ofString "ns"),.load .one (fundingAddress 8),.panop .mul [.var .local (ofString "sp"),.const 32]]) (stackPushGrowthAt 5):=rfl
theorem source_stack_push_growth_5 : stackPushGrowthAt 5=.seq (.store (fundingAddress 8) (.var .local (ofString "ns"))) (.store (fundingAddress 232) (.var .local (ofString "ncap"))):=rfl
#print axioms source_stack_push_growth_0
#print axioms source_stack_push_growth_1
#print axioms source_stack_push_growth_2
#print axioms source_stack_push_growth_3
#print axioms source_stack_push_growth_4
#print axioms source_stack_push_growth_5
end InitECandidate.Runtime

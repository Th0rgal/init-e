import InitECandidate.Runtime.FrameNewSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def stackPopAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_stack_pop)
theorem source_stack_pop_0 : stackPopAt 0=.dec (ofString "sp") .one (fundingLoad 16) (stackPopAt 1):=rfl
theorem source_stack_pop_1 : stackPopAt 1=.seq (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0)) (.raise (ofString "EvmErr") (.const 2)) .skip) (stackPopAt 2):=rfl
theorem source_stack_pop_2 : stackPopAt 2=.seq (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"),.const 1])) (stackPopAt 3):=rfl
theorem source_stack_pop_3 : stackPopAt 3=.seq (.store (fundingAddress 16) (.var .local (ofString "sp"))) (stackPopAt 4):=rfl
theorem source_stack_pop_4 : stackPopAt 4=.return (.load (.comb [.one,.one,.one,.one]) (.op .add [fundingLoad 8,.panop .mul [.var .local (ofString "sp"),.const 32]])):=rfl
#print axioms source_stack_pop_0
#print axioms source_stack_pop_1
#print axioms source_stack_pop_2
#print axioms source_stack_pop_3
#print axioms source_stack_pop_4
end InitECandidate.Runtime

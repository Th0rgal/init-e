import InitECandidate.Runtime.FrameNewSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stackPushAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_stack_push)
def stackPushBase : ExpHOL 64:=.op .add [.load .one (fundingAddress 8),.panop .mul [.var .local (ofString "sp"),.const 32]]

theorem source_stack_push_0 : stackPushAt 0=.dec (ofString "sp") .one (.load .one (fundingAddress 16)) (stackPushAt 1):=rfl
theorem source_stack_push_1 : stackPushAt 1=.dec (ofString "cap") .one (.load .one (fundingAddress 232)) (stackPushAt 2):=rfl
theorem source_stack_push_2 : stackPushAt 2=.seq (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))
 (match stackPushAt 2 with | .seq (.ite _ branch _) _=>branch | _=>.skip) .skip) (stackPushAt 3):=rfl
theorem source_stack_push_3 : stackPushAt 3=.seq (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 1024)) (.raise (ofString "EvmErr") (.const 3)) .skip) (stackPushAt 4):=rfl
theorem source_stack_push_4 : stackPushAt 4=.seq (.store stackPushBase (.var .local (ofString "v"))) (stackPushAt 5):=rfl
theorem source_stack_push_5 : stackPushAt 5=.seq (.store (fundingAddress 16) (.op .add [.var .local (ofString "sp"),.const 1])) (stackPushAt 6):=rfl
theorem source_stack_push_6 : stackPushAt 6=.return (.const 0):=rfl
#print axioms source_stack_push_0
#print axioms source_stack_push_1
#print axioms source_stack_push_2
#print axioms source_stack_push_3
#print axioms source_stack_push_4
#print axioms source_stack_push_5
#print axioms source_stack_push_6
end InitECandidate.Runtime

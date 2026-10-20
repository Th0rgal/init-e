import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def computeJumpdestsAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_compute_jumpdests)
def computeJumpdestsCondition : ExpHOL 64 := match computeJumpdestsAt 3 with
 | .seq (.while condition _) _=>condition | _=>.const 0
def computeJumpdestsLoopBody : ProgHOL 64 := match computeJumpdestsAt 3 with
 | .seq (.while _ body) _=>body | _=>.skip
def computeJumpdestsOpcodeRest : ProgHOL 64 := match computeJumpdestsLoopBody with
 | .dec _ _ _ (.dec _ _ _ (.seq (.ite _ _ other) _))=>other | _=>.skip
def computeJumpdestsStoreAddress : ExpHOL 64 :=
 .op .add [.var .local (ofString "bm"),.panop .mul [.shift .lsr (.var .local (ofString "pc")) (.const 6),.const 8]]
def computeJumpdestsStoreValue : ExpHOL 64 :=
 .op .or [.load .one computeJumpdestsStoreAddress,
  .shift .lsl (.const 1) (.op .and [.var .local (ofString "pc"),.const 63])]
def computeJumpdestsOpcodeInitializer : ExpHOL 64 :=
 .loadByte (.op .add [.var .local (ofString "code"),.var .local (ofString "pc")])
def computeJumpdestsAdvance : ProgHOL 64 :=
 .assign .local (ofString "pc") (.op .add [.var .local (ofString "pc"),.var .local (ofString "adv")])

def computeJumpdestsSizeExpression : ExpHOL 64 :=
 .op .add [.panop .mul [.shift .lsr (.op .add [.var .local (ofString "n"),.const 63]) (.const 6),.const 8],.const 8]
theorem source_compute_jumpdests_entry : computeJumpdestsAt 0=
 .decCall (ofString "bm") .one (ofString "scratch_alloc") [computeJumpdestsSizeExpression] (computeJumpdestsAt 1) := rfl
theorem source_compute_jumpdests_zero : computeJumpdestsAt 1=
 .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "bm"),computeJumpdestsSizeExpression])
  (computeJumpdestsAt 2) := rfl
theorem source_compute_jumpdests_pc : computeJumpdestsAt 2=.dec (ofString "pc") .one (.const 0) (computeJumpdestsAt 3) := rfl

theorem source_compute_jumpdests_loop : computeJumpdestsAt 3=
 .seq (.while computeJumpdestsCondition computeJumpdestsLoopBody) (computeJumpdestsAt 4) := rfl

theorem source_compute_jumpdests_body : computeJumpdestsLoopBody=
 .dec (ofString "op") .one computeJumpdestsOpcodeInitializer
  (.dec (ofString "adv") .one (.const 1)
   (.seq (.ite (.cmp .equal (.var .local (ofString "op")) (.const 91))
    (.store computeJumpdestsStoreAddress computeJumpdestsStoreValue) computeJumpdestsOpcodeRest) computeJumpdestsAdvance)) := rfl
#print axioms source_compute_jumpdests_entry
#print axioms source_compute_jumpdests_zero
#print axioms source_compute_jumpdests_pc
#print axioms source_compute_jumpdests_loop
#print axioms source_compute_jumpdests_body
end InitECandidate.Runtime

import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def scratchHashAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htab_new_scratch)
def scratchHashAddress (offset : BitVec 64) : ExpHOL 64 := .op .add [.var .local (ofString "t"),.const offset]
def scratchHashStrideExpression : ExpHOL 64 :=
 .op .and [.op .add [.var .local (ofString "key_len"),.const 7],.op .sub [.const 0,.const 8]]
def scratchHashSizeExpression (argument : ExpHOL 64) : ExpHOL 64 :=
 .panop .mul [.var .local (ofString "cap"),argument]

theorem source_scratch_hash_0 : scratchHashAt 0=.decCall (ofString "t") .one (ofString "scratch_alloc") [.const 72] (scratchHashAt 1) := rfl
theorem source_scratch_hash_1 : scratchHashAt 1=.dec (ofString "stride") .one scratchHashStrideExpression (scratchHashAt 2) := rfl
theorem source_scratch_hash_2 : scratchHashAt 2=
 .seq (.store (scratchHashAddress 0) (.var .local (ofString "key_len")))
  (.seq (.store (scratchHashAddress 8) (.var .local (ofString "stride")))
   (.seq (.store (scratchHashAddress 16) (.var .local (ofString "cap")))
    (.seq (.store (scratchHashAddress 24) (.const 0)) (scratchHashAt 6)))) := rfl
theorem source_scratch_hash_6 : scratchHashAt 6=.decCall (ofString "keys") .one (ofString "scratch_alloc")
 [scratchHashSizeExpression (.var .local (ofString "stride"))] (scratchHashAt 7) := rfl
theorem source_scratch_hash_7 : scratchHashAt 7=.seq (.store (scratchHashAddress 32) (.var .local (ofString "keys"))) (scratchHashAt 8) := rfl
theorem source_scratch_hash_8 : scratchHashAt 8=.decCall (ofString "vals") .one (ofString "scratch_alloc")
 [scratchHashSizeExpression (.const 8)] (scratchHashAt 9) := rfl
theorem source_scratch_hash_9 : scratchHashAt 9=.seq (.store (scratchHashAddress 40) (.var .local (ofString "vals"))) (scratchHashAt 10) := rfl
theorem source_scratch_hash_10 : scratchHashAt 10=.decCall (ofString "used") .one (ofString "scratch_alloc")
 [.var .local (ofString "cap")] (scratchHashAt 11) := rfl
theorem source_scratch_hash_11 : scratchHashAt 11=.seq (.call (some (none,none)) (ofString "memzero")
 [.var .local (ofString "used"),.var .local (ofString "cap")]) (scratchHashAt 12) := rfl
theorem source_scratch_hash_12 : scratchHashAt 12=.seq (.store (scratchHashAddress 48) (.var .local (ofString "used"))) (scratchHashAt 13) := rfl
theorem source_scratch_hash_13 : scratchHashAt 13=.decCall (ofString "order") .one (ofString "scratch_alloc")
 [scratchHashSizeExpression (.const 8)] (scratchHashAt 14) := rfl
theorem source_scratch_hash_14 : scratchHashAt 14=.seq (.store (scratchHashAddress 56) (.var .local (ofString "order"))) (scratchHashAt 15) := rfl
theorem source_scratch_hash_15 : scratchHashAt 15=.decCall (ofString "order_pos") .one (ofString "scratch_alloc")
 [scratchHashSizeExpression (.const 8)] (scratchHashAt 16) := rfl
theorem source_scratch_hash_16 : scratchHashAt 16=.seq (.store (scratchHashAddress 64) (.var .local (ofString "order_pos"))) (scratchHashAt 17) := rfl
theorem source_scratch_hash_17 : scratchHashAt 17=.return (.var .local (ofString "t")) := rfl
#print axioms source_scratch_hash_0
#print axioms source_scratch_hash_1
#print axioms source_scratch_hash_2
#print axioms source_scratch_hash_6
#print axioms source_scratch_hash_7
#print axioms source_scratch_hash_8
#print axioms source_scratch_hash_9
#print axioms source_scratch_hash_10
#print axioms source_scratch_hash_11
#print axioms source_scratch_hash_12
#print axioms source_scratch_hash_13
#print axioms source_scratch_hash_14
#print axioms source_scratch_hash_15
#print axioms source_scratch_hash_16
#print axioms source_scratch_hash_17
end InitECandidate.Runtime

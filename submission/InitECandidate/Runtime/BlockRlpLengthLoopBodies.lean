import InitECandidate.Runtime.BlockRlpLengthLoopDeclaration
import InitECandidate.Runtime.RlpBytesEncodedLengthRuntimeBound
import InitECandidate.Runtime.WithdrawalRlpLengthRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def blockRlpLengthLoopAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_block_rlp_length)
def blockRlpTxBody : ProgHOL 64 :=
 match blockRlpLengthLoopAt 8 with
 | .seq (.while _ body) _=>body
 | _=>.skip
def blockRlpWdBody : ProgHOL 64 :=
 match blockRlpLengthLoopAt 15 with
 | .seq (.while _ body) _=>body
 | _=>.skip
def blockRlpTxAt (index : Nat) : ProgHOL 64 := (statelessNext^[index]) blockRlpTxBody
def blockRlpTxInit (index : Nat) : ExpHOL 64 :=
 match blockRlpTxAt index with
 | .dec _ _ value _=>value
 | _=>.const 0
def blockRlpTxGuard (index : Nat) : ProgHOL 64 :=
 match blockRlpTxAt index with
 | .seq first _=>first
 | _=>.skip
def blockRlpTxLengthCondition : ExpHOL 64 :=
 match blockRlpTxGuard 4 with
 | .ite condition _ _=>condition
 | _=>.const 0
def blockRlpWdArguments : List (ExpHOL 64) :=
 match blockRlpWdBody with
 | .decCall _ _ _ args _=>args
 | _=>[]
def blockRlpTxIterationCost : Nat := ((2^64-1)+2)+1
def blockRlpWdIterationCost : Nat := withdrawalRlpLengthSourceCost+1

theorem source_block_rlp_tx_body :
 blockRlpTxAt 0=.dec (ofString "n") .one (blockRlpTxInit 0) (blockRlpTxAt 1) ∧
 blockRlpTxAt 1=.dec (ofString "fb") .one (.const 0) (blockRlpTxAt 2) ∧
 blockRlpTxAt 2=.seq (blockRlpTxGuard 2) (blockRlpTxAt 3) ∧
 blockRlpTxAt 3=.dec (ofString "el") .one (.var .local (ofString "n")) (blockRlpTxAt 4) ∧
 blockRlpTxAt 4=.seq (blockRlpTxGuard 4) (blockRlpTxAt 5) ∧
 blockRlpTxGuard 4=.ite blockRlpTxLengthCondition
  (.call (some (some (.local,ofString "el"),none)) (ofString "rlp_bytes_encoded_len")
   [.var .local (ofString "fb"),.var .local (ofString "n")]) .skip ∧
 blockRlpTxAt 5=.seq (.assign .local (ofString "tl") (.op .add [.var .local (ofString "tl"),.var .local (ofString "el")]))
  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem source_block_rlp_wd_body : blockRlpWdBody=
 .decCall (ofString "wlen") .one (ofString "withdrawal_rlp_len") blockRlpWdArguments
  (.seq (.assign .local (ofString "wl") (.op .add [.var .local (ofString "wl"),.var .local (ofString "wlen")]))
   (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) := rfl

theorem block_rlp_tx_counted : BlockRlpCountedBody (ofString "i") blockRlpTxBody blockRlpTxIterationCost := by
 obtain ⟨n,fb,first,el,guard,encoded,tail⟩:=source_block_rlp_tx_body
 have guardBound : ProgBounded (blockRlpTxGuard 4) blockRlpTxIterationCost := by
  rw [encoded]
  exact ProgBounded.ite _ (ProgBounded.call rlp_bytes_length_fun_bounded _ _)
   (ProgBounded.weaken (ProgBounded.straight _ rfl) (by omega))
 have b5 : ProgBounded (blockRlpTxAt 5) 0 := ProgBounded.straight _ (by decide_cbv)
 have b4 : ProgBounded (blockRlpTxAt 4) blockRlpTxIterationCost := by
  rw [guard]
  intro F state code budget
  exact ProgBounded.seq guardBound b5 state code (by simpa using budget)
 have b3 : ProgBounded (blockRlpTxAt 3) blockRlpTxIterationCost := by
  rw [el];exact ProgBounded.dec _ _ _ b4
 have b2 : ProgBounded (blockRlpTxAt 2) blockRlpTxIterationCost := by
  rw [first]
  have straight : ProgBounded (blockRlpTxGuard 2) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq straight b3 state code (by simpa using budget)
 have b1 : ProgBounded (blockRlpTxAt 1) blockRlpTxIterationCost := by
  rw [fb];exact ProgBounded.dec _ _ _ b2
 have b0 : ProgBounded (blockRlpTxAt 0) blockRlpTxIterationCost := by
  rw [n];exact ProgBounded.dec _ _ _ b1
 have a5 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 5) := by
  rw [tail];exact block_rlp_counter_seq _ _ _ (by decide) (block_rlp_counter_incr _)
 have a4 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 4) := by
  rw [guard];exact block_rlp_counter_seq _ _ _ (by decide_cbv) a5
 have a3 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 3) := by
  rw [el];exact block_rlp_counter_dec _ _ _ _ _ (by decide) a4
 have a2 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 2) := by
  rw [first];exact block_rlp_counter_seq _ _ _ (by decide_cbv) a3
 have a1 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 1) := by
  rw [fb];exact block_rlp_counter_dec _ _ _ _ _ (by decide) a2
 have a0 : BlockRlpCounterAdvances (ofString "i") (blockRlpTxAt 0) := by
  rw [n];exact block_rlp_counter_dec _ _ _ _ _ (by decide) a1
 exact ⟨b0,by decide_cbv,a0⟩
theorem block_rlp_wd_counted : BlockRlpCountedBody (ofString "i") blockRlpWdBody blockRlpWdIterationCost := by
 rw [source_block_rlp_wd_body]
 refine ⟨?_,by decide_cbv,?_⟩
 · intro F state code budget
   exact ProgBounded.decCall withdrawal_rlp_length_fun_bounded (ofString "wlen") .one blockRlpWdArguments
    (ProgBounded.straight (.seq (.assign .local (ofString "wl") (.op .add [.var .local (ofString "wl"),.var .local (ofString "wlen")]))
     (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) (by decide)) state code (by simpa [blockRlpWdIterationCost] using budget)
 · exact block_rlp_counter_decCall _ _ _ _ _ _ (by decide)
    (block_rlp_counter_seq _ _ _ (by decide) (block_rlp_counter_incr _))
#print axioms block_rlp_tx_counted
#print axioms block_rlp_wd_counted
end InitECandidate.Runtime

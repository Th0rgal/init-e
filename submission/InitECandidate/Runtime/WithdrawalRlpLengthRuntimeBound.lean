import InitECandidate.Runtime.RlpLengthRuntimeBounds
import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.OriginalWithdrawalLengthCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Only the actual statement spine is split; all byte loads remain in the original arguments. -/
def withdrawalRlpLengthAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_withdrawal_rlp_len)
def withdrawalRlpLengthArguments (index : Nat) : List (ExpHOL 64) :=
 match withdrawalRlpLengthAt index with
 | .decCall _ _ _ args _=>args
 | _=>[]
def withdrawalRlpLengthPayload : ExpHOL 64 :=
 match withdrawalRlpLengthAt 3 with
 | .dec _ _ value _=>value
 | _=>.const 0

theorem source_withdrawal_rlp_length_calls :
 withdrawalRlpLengthAt 0=.decCall (ofString "a") .one (ofString "rlp_word_encoded_len")
  (withdrawalRlpLengthArguments 0) (withdrawalRlpLengthAt 1) ∧
 withdrawalRlpLengthAt 1=.decCall (ofString "b") .one (ofString "rlp_word_encoded_len")
  (withdrawalRlpLengthArguments 1) (withdrawalRlpLengthAt 2) ∧
 withdrawalRlpLengthAt 2=.decCall (ofString "c") .one (ofString "rlp_word_encoded_len")
  (withdrawalRlpLengthArguments 2) (withdrawalRlpLengthAt 3) ∧
 withdrawalRlpLengthAt 3=.dec (ofString "payload") .one withdrawalRlpLengthPayload (withdrawalRlpLengthAt 4) ∧
 withdrawalRlpLengthAt 4=.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
  (withdrawalRlpLengthArguments 4) (withdrawalRlpLengthAt 5) := by
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩

def withdrawalRlpLengthSourceCost : Nat := 3*((2^64-1)+2)+((2^64-1)+3)
/-- The complete original withdrawal-length routine has a fixed finite source bound.
Its real byte-load arguments may fail; no readability or decoded-value assumption is needed. -/
theorem withdrawal_rlp_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_withdrawal_rlp_len) withdrawalRlpLengthSourceCost := by
 obtain ⟨first,second,third,payload,last⟩:=source_withdrawal_rlp_length_calls
 let W : Nat := (2^64-1)+1
 let L : Nat := ((2^64-1)+1)+1
 have returned : ProgBounded (withdrawalRlpLengthAt 5) 0 := ProgBounded.straight _ (by decide_cbv)
 have header : ProgBounded (withdrawalRlpLengthAt 4) (L+1+0) := by
  rw [last]
  exact ProgBounded.decCall rlp_list_header_length_fun_bounded _ _ _ returned
 have declared : ProgBounded (withdrawalRlpLengthAt 3) (L+1+0) := by
  rw [payload]
  exact ProgBounded.dec (ofString "payload") .one withdrawalRlpLengthPayload header
 have c : ProgBounded (withdrawalRlpLengthAt 2) (W+1+(L+1+0)) := by
  rw [third]
  exact ProgBounded.decCall rlp_word_length_fun_bounded _ _ _ declared
 have b : ProgBounded (withdrawalRlpLengthAt 1) (W+1+(W+1+(L+1+0))) := by
  rw [second]
  exact ProgBounded.decCall rlp_word_length_fun_bounded _ _ _ c
 have a : ProgBounded (withdrawalRlpLengthAt 0) (W+1+(W+1+(W+1+(L+1+0)))) := by
  rw [first]
  exact ProgBounded.decCall rlp_word_length_fun_bounded _ _ _ b
 have ceiling : W+1+(W+1+(W+1+(L+1+0)))≤withdrawalRlpLengthSourceCost := by decide
 have bounded : ProgBounded (withdrawalRlpLengthAt 0) withdrawalRlpLengthSourceCost := ProgBounded.weaken a ceiling
 intro F state code budget
 rw [sourceFunctionBody_eq_structural]
 exact bounded state code budget
theorem withdrawal_rlp_length_fun_bounded : FunBounded (ofString "withdrawal_rlp_len") withdrawalRlpLengthSourceCost :=
 ⟨_,_,_,originalRuntimeCode_withdrawalRlpLength_lookup,withdrawal_rlp_length_body_bounded⟩
#print axioms withdrawal_rlp_length_fun_bounded
#print axioms withdrawal_rlp_length_body_bounded
end InitECandidate.Runtime

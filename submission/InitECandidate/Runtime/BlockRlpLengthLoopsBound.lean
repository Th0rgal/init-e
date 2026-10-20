import InitECandidate.Runtime.BlockRlpLengthLoopBodies
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def blockRlpLengthLoopInit (index : Nat) : ExpHOL 64 :=
 match blockRlpLengthLoopAt index with
 | .dec _ _ value _=>value
 | _=>.const 0
def blockRlpLengthLoopFirst (index : Nat) : ProgHOL 64 :=
 match blockRlpLengthLoopAt index with
 | .seq first _=>first
 | _=>.skip
def blockRlpLengthLoopArguments (index : Nat) : List (ExpHOL 64) :=
 match blockRlpLengthLoopAt index with
 | .seq (.call _ _ args) _=>args
 | .decCall _ _ _ args _=>args
 | _=>[]
def blockRlpLengthTxLoopCost : Nat := (2^64-1)*(blockRlpTxIterationCost+1)
def blockRlpLengthWdLoopCost : Nat := (2^64-1)*(blockRlpWdIterationCost+1)
def blockRlpLengthLoopSuffixCost : Nat := blockRlpLengthTxLoopCost+(((2^64-1)+3)+(blockRlpLengthWdLoopCost+(((2^64-1)+3)+((2^64-1)+3))))

theorem source_block_rlp_length_loop_stages :
 blockRlpLengthLoopAt 3=.dec (ofString "total") .one (blockRlpLengthLoopInit 3) (blockRlpLengthLoopAt 4) ∧
 blockRlpLengthLoopAt 4=.dec (ofString "txs") .one (blockRlpLengthLoopInit 4) (blockRlpLengthLoopAt 5) ∧
 blockRlpLengthLoopAt 5=.dec (ofString "ntx") .one (blockRlpLengthLoopInit 5) (blockRlpLengthLoopAt 6) ∧
 blockRlpLengthLoopAt 6=.dec (ofString "tl") .one (.const 0) (blockRlpLengthLoopAt 7) ∧
 blockRlpLengthLoopAt 7=.dec (ofString "i") .one (.const 0)
  (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) blockRlpTxBody) (blockRlpLengthLoopAt 9)) ∧
 blockRlpLengthLoopAt 9=.decCall (ofString "hl") .one (ofString "rlp_list_header_len") (blockRlpLengthLoopArguments 9) (blockRlpLengthLoopAt 10) ∧
 blockRlpLengthLoopAt 10=.seq (blockRlpLengthLoopFirst 10) (blockRlpLengthLoopAt 11) ∧
 blockRlpLengthLoopAt 11=.seq (blockRlpLengthLoopFirst 11) (blockRlpLengthLoopAt 12) ∧
 blockRlpLengthLoopAt 12=.dec (ofString "nwd") .one (blockRlpLengthLoopInit 12) (blockRlpLengthLoopAt 13) ∧
 blockRlpLengthLoopAt 13=.dec (ofString "wl") .one (.const 0) (blockRlpLengthLoopAt 14) ∧
 blockRlpLengthLoopAt 14=.seq (.assign .local (ofString "i") (.const 0))
  (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) blockRlpWdBody) (blockRlpLengthLoopAt 16)) ∧
 blockRlpLengthLoopAt 16=.seq (.call (some (some (.local,ofString "hl"),none)) (ofString "rlp_list_header_len") (blockRlpLengthLoopArguments 16)) (blockRlpLengthLoopAt 17) ∧
 blockRlpLengthLoopAt 17=.seq (blockRlpLengthLoopFirst 17) (blockRlpLengthLoopAt 18) ∧
 blockRlpLengthLoopAt 18=.seq (.call (some (some (.local,ofString "hl"),none)) (ofString "rlp_list_header_len") (blockRlpLengthLoopArguments 18)) (blockRlpLengthLoopAt 19) := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The complete actual transaction/withdrawal length suffix (starting just
 after header encoding/release) has a fixed finite source bound. All actual
 loads may fail, and no readable-memory or successful-callee premise is required. -/
theorem block_rlp_length_loop_suffix_bounded : ProgBounded (blockRlpLengthLoopAt 3) blockRlpLengthLoopSuffixCost := by
 obtain ⟨s3,s4,s5,s6,s7,s9,s10,s11,s12,s13,s14,s16,s17,s18⟩:=source_block_rlp_length_loop_stages
 let L : Nat := (2^64-1)+3
 have b19 : ProgBounded (blockRlpLengthLoopAt 19) 0 := ProgBounded.straight _ (by decide_cbv)
 have b18 : ProgBounded (blockRlpLengthLoopAt 18) L := by
  rw [s18]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_list_header_length_fun_bounded _ _) b19 state code (by change ((2^64-1)+2)+1+0≤state.clock;simpa [L] using budget)
 have b17 : ProgBounded (blockRlpLengthLoopAt 17) L := by
  rw [s17]
  have first : ProgBounded (blockRlpLengthLoopFirst 17) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  simpa only [Nat.zero_add] using (ProgBounded.seq first b18 state code (by simpa only [Nat.zero_add] using budget))
 have b16 : ProgBounded (blockRlpLengthLoopAt 16) (L+L) := by
  rw [s16]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_list_header_length_fun_bounded _ _) b17 state code (by change ((2^64-1)+2)+1+L≤state.clock;simpa [L] using budget)
 have b14 : ProgBounded (blockRlpLengthLoopAt 14) (blockRlpLengthWdLoopCost+(L+L)) := by
  rw [s14]
  exact ProgBounded.blockRlpCountedAssign _ _ .less (Or.inl rfl) block_rlp_wd_counted (by decide_cbv) b16
 have b13 : ProgBounded (blockRlpLengthLoopAt 13) (blockRlpLengthWdLoopCost+(L+L)) := by
  rw [s13];exact ProgBounded.dec _ _ _ b14
 have b12 : ProgBounded (blockRlpLengthLoopAt 12) (blockRlpLengthWdLoopCost+(L+L)) := by
  rw [s12];exact ProgBounded.dec _ _ _ b13
 have b11 : ProgBounded (blockRlpLengthLoopAt 11) (blockRlpLengthWdLoopCost+(L+L)) := by
  rw [s11]
  have first : ProgBounded (blockRlpLengthLoopFirst 11) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  simpa only [Nat.zero_add] using (ProgBounded.seq (a:=0) (b:=blockRlpLengthWdLoopCost+(L+L)) first b12 state code (by simpa only [Nat.zero_add] using budget))
 have b10 : ProgBounded (blockRlpLengthLoopAt 10) (blockRlpLengthWdLoopCost+(L+L)) := by
  rw [s10]
  have first : ProgBounded (blockRlpLengthLoopFirst 10) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  simpa only [Nat.zero_add] using (ProgBounded.seq (a:=0) (b:=blockRlpLengthWdLoopCost+(L+L)) first b11 state code (by simpa only [Nat.zero_add] using budget))
 have b9 : ProgBounded (blockRlpLengthLoopAt 9) (L+(blockRlpLengthWdLoopCost+(L+L))) := by
  rw [s9]
  intro F state code budget
  exact ProgBounded.decCall rlp_list_header_length_fun_bounded _ _ _ b10 state code (by change ((2^64-1)+2)+1+_≤state.clock;simpa [L] using budget)
 have b7 : ProgBounded (blockRlpLengthLoopAt 7) blockRlpLengthLoopSuffixCost := by
  rw [s7]
  exact ProgBounded.blockRlpCountedDec _ _ .less (Or.inl rfl) block_rlp_tx_counted (by decide_cbv) b9
 have b6 : ProgBounded (blockRlpLengthLoopAt 6) blockRlpLengthLoopSuffixCost := by
  rw [s6];exact ProgBounded.dec _ _ _ b7
 have b5 : ProgBounded (blockRlpLengthLoopAt 5) blockRlpLengthLoopSuffixCost := by
  rw [s5];exact ProgBounded.dec _ _ _ b6
 have b4 : ProgBounded (blockRlpLengthLoopAt 4) blockRlpLengthLoopSuffixCost := by
  rw [s4];exact ProgBounded.dec _ _ _ b5
 rw [s3]
 intro F state code budget
 exact ProgBounded.dec (ofString "total") .one (blockRlpLengthLoopInit 3) b4 state code budget
#print axioms source_block_rlp_length_loop_stages
#print axioms block_rlp_length_loop_suffix_bounded
end InitECandidate.Runtime

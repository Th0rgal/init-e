import InitECandidate.Runtime.MemoryMul64SchoolbookReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual schoolbook square cannot report a zero high word for a large
word count. Its input already has the real words_of right-shift ceiling. -/
theorem memory_mul64_square_high_zero_ceiling (word : BitVec 64)
 (small : word.toNat<2^59) (zero : (memoryMul64Schoolbook word word).2=0#64) :
 word.toNat<2^32 := by
 let low:=word&&&4294967295#64
 let high:=word>>>(32:Nat)
 let cross:=low*high
 let square:=high*high
 let mid:=wordAddCarryHOL cross cross (0#64)
 let lo:=wordAddCarryHOL (low*low) (mid.1<<<(32:Nat)) (0#64)
 have lowBound : low.toNat≤4294967295 := by
  change (word&&&4294967295#64).toNat≤4294967295
  rw [BitVec.toNat_and]
  change word.toNat&&&(2^32-1)≤4294967295
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have bounded:=Nat.mod_lt word.toNat (show 0<2^32 by decide)
  omega
 have highNat : high.toNat=word.toNat/2^32 := by simp [high,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 have highBound : high.toNat≤134217727 := by rw [highNat];omega
 have productBound:=Nat.mul_le_mul lowBound highBound
 have squareBound:=Nat.mul_le_mul highBound highBound
 have crossNat : cross.toNat=low.toNat*high.toNat := by
  exact BitVec.toNat_mul_of_lt (by omega)
 have squareNat : square.toNat=high.toNat*high.toNat := by
  exact BitVec.toNat_mul_of_lt (by omega)
 have sumSmall : cross.toNat+cross.toNat<2^64 := by rw [crossNat];omega
 have midCarry : mid.2=0#64 := by simp [mid,wordAddCarryHOL] <;> omega
 have midNat : mid.1.toNat=cross.toNat+cross.toNat := by
  simp [mid,wordAddCarryHOL,BitVec.toNat_ofNat,Nat.mod_eq_of_lt] <;> omega
 have midBound : mid.1.toNat<2^60 := by rw [midNat,crossNat];omega
 have shiftNat : (mid.1>>>(32:Nat)).toNat=mid.1.toNat/2^32 := by rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 have shiftBound : (mid.1>>>(32:Nat)).toNat<2^28 := by rw [shiftNat];omega
 have carryBound : lo.2.toNat≤1 := by
  simp only [lo,wordAddCarryHOL]
  split <;> first | decide | (split <;> decide)
 have firstSmall : square.toNat+(mid.1>>>(32:Nat)).toNat<2^64 := by rw [squareNat];omega
 have allSmall : (square+(mid.1>>>(32:Nat))).toNat+lo.2.toNat<2^64 := by
  rw [BitVec.toNat_add_of_lt firstSmall,squareNat];omega
 have crossComm : high*low=low*high:=BitVec.mul_comm _ _
 simp only [memoryMul64Schoolbook] at zero
 change square+((wordAddCarryHOL cross (high*low) (0#64)).1>>>(32:Nat))+((wordAddCarryHOL cross (high*low) (0#64)).2<<<(32:Nat))+(wordAddCarryHOL (low*low) ((wordAddCarryHOL cross (high*low) (0#64)).1<<<(32:Nat)) (0#64)).2=0#64 at zero
 rw [crossComm] at zero
 change square+(mid.1>>>(32:Nat))+(mid.2<<<(32:Nat))+lo.2=0#64 at zero
 rw [midCarry,BitVec.zero_shiftLeft,BitVec.add_zero] at zero
 have natural:=congrArg BitVec.toNat zero
 rw [BitVec.toNat_add_of_lt allSmall,BitVec.toNat_add_of_lt firstSmall,squareNat] at natural
 have squareZero : high.toNat*high.toNat=0 := by change _=0 at natural;omega
 have highZero : high.toNat=0 := by
  by_contra notZero
  have positive:=Nat.pos_of_ne_zero notZero
  have productPositive:=Nat.mul_pos positive positive
  omega
 rw [highNat] at highZero
 omega
#print axioms memory_mul64_square_high_zero_ceiling
end InitECandidate.Runtime

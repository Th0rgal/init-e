import InitECandidate.Runtime.ChargeGasCallFootprint
import InitECandidate.Runtime.ChargeGasProgress
import InitECandidate.Runtime.ChildFunding
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Concrete funding words in a live original 280-byte EVM frame record. -/
structure InterpreterFundingFrame where
 address : BitVec 64
 gas : GasFunding
 stateGas : BitVec 64

def interpreterFundingOffsets : List (BitVec 64) := [64,72,184,192]
structure InterpreterFundingFrameAt {F : Type} (s : PanSemStateFiniteExact 64 F)
 (lower upper : Nat) (frame : InterpreterFundingFrame) : Prop where
 lowerBound : lower≤frame.address.toNat
 extent : frame.address.toNat+280≤upper
 aligned : frame.address.toNat%8=0
 readable : ∀offset∈interpreterFundingOffsets,s.memaddrs (frame.address+offset)
 funding : HasGasFunding s frame.address frame.gas
 stateGasAt : s.memory (frame.address+72)=.word frame.stateGas

def interpreterFundingDisjoint (a b : InterpreterFundingFrame) : Prop :=
 a.address.toNat+280≤b.address.toNat ∨b.address.toNat+280≤a.address.toNat

def interpreterFundingPotential : List InterpreterFundingFrame→Nat
 | []=>0
 | frame::rest=>frame.gas.potential+interpreterFundingPotential rest

def interpreterFundingUsed : List InterpreterFundingFrame→Nat
 | []=>0
 | frame::rest=>frame.gas.used.toNat+interpreterFundingUsed rest
/-- Physical, readable, pairwise disjoint original records plus the global
regular-funding budget. No execution/rank callback is stored in this predicate. -/
structure InterpreterFundingLayout {F : Type} (s : PanSemStateFiniteExact 64 F)
 (lower upper : Nat) (frames : List InterpreterFundingFrame) : Prop where
 upperBound : upper≤2^64
 records : ∀frame∈frames,InterpreterFundingFrameAt s lower upper frame
 disjoint : frames.Pairwise interpreterFundingDisjoint
 budget : interpreterFundingPotential frames≤200000000

theorem interpreter_funding_offset_natural (frame : InterpreterFundingFrame) (upper : Nat)
 (extent : frame.address.toNat+280≤upper) (cap : upper≤2^64)
 (offset : BitVec 64) (small : offset.toNat<280) :
 (frame.address+offset).toNat=frame.address.toNat+offset.toNat :=
 BitVec.toNat_add_of_lt (by omega)

theorem interpreter_funding_offsets_distinct (a b : InterpreterFundingFrame) (upper : Nat)
 (aExtent : a.address.toNat+280≤upper) (bExtent : b.address.toNat+280≤upper)
 (cap : upper≤2^64) (separate : interpreterFundingDisjoint a b)
 (ka kb : BitVec 64) (aSmall : ka.toNat<280) (bSmall : kb.toNat<280) :
 a.address+ka≠b.address+kb := by
 intro equal
 have natural:=congrArg BitVec.toNat equal
 rw [interpreter_funding_offset_natural a upper aExtent cap ka aSmall,
  interpreter_funding_offset_natural b upper bExtent cap kb bSmall] at natural
 rcases separate with before|after <;>omega

theorem InterpreterFundingFrameAt.after_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {lower upper : Nat} {frame : InterpreterFundingFrame}
 (valid : InterpreterFundingFrameAt s lower upper frame)
 (domain : post.memaddrs=s.memaddrs)
 (memory : ∀offset∈interpreterFundingOffsets,post.memory (frame.address+offset)=s.memory (frame.address+offset)) :
 InterpreterFundingFrameAt post lower upper frame := by
 constructor
 · exact valid.lowerBound
 · exact valid.extent
 · exact valid.aligned
 · intro offset present;rw [domain];exact valid.readable offset present
 · rcases valid.funding with ⟨left,used,spill⟩
   exact ⟨(memory 64 (by simp [interpreterFundingOffsets])).trans left,
    (memory 184 (by simp [interpreterFundingOffsets])).trans used,
    (memory 192 (by simp [interpreterFundingOffsets])).trans spill⟩
 · exact (memory 72 (by simp [interpreterFundingOffsets])).trans valid.stateGasAt
#print axioms interpreter_funding_offset_natural
#print axioms interpreter_funding_offsets_distinct
#print axioms InterpreterFundingFrameAt.after_frame
end InitECandidate.Runtime

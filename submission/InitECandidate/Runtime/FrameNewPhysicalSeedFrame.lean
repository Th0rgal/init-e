import InitECandidate.Runtime.FrameNewWholePhysicalSeed
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxHeartbeats 2000000
/-- An actual lower scratch continuation cannot change an older frame seed. -/
theorem FrameNewPhysicalSeed.after_upper_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record scratch frame codePointer codeLength message : BitVec 64}
 (valid : FrameNewPhysicalSeed s record scratch frame codePointer codeLength message)
 (post : PanSemStateFiniteExact 64 F)
 (memory : ∀watched : BitVec 64,record.toNat≤watched.toNat → post.memory watched=s.memory watched) :
 FrameNewPhysicalSeed post record scratch frame codePointer codeLength message := by
 have atWord (offset : BitVec 64) (small : offset.toNat<280) : post.memory (record+offset)=s.memory (record+offset) := by
  apply memory
  have extent:=valid.extent
  have bound:=scratch.isLt
  rw [BitVec.toNat_add_of_lt (by omega)]
  omega
 exact ⟨valid.extent,valid.aligned,valid.stackExtent,valid.memoryExtent,valid.memoryBeforeStack,
  (atWord 8 (by decide)).trans valid.stackAt,(atWord 16 (by decide)).trans valid.stackSizeAt,
  (atWord 24 (by decide)).trans valid.memoryAt,(atWord 32 (by decide)).trans valid.memorySizeAt,
  (atWord 40 (by decide)).trans valid.memoryCapacityAt,(atWord 48 (by decide)).trans valid.codeAt,
  (atWord 56 (by decide)).trans valid.codeLengthAt,(atWord 104 (by decide)).trans valid.activeAt,
  (atWord 112 (by decide)).trans valid.messageAt,(atWord 128 (by decide)).trans valid.returnSizeAt,
  (atWord 160 (by decide)).trans valid.errorAt,(atWord 200 (by decide)).trans valid.stateUsedAt,
  (atWord 232 (by decide)).trans valid.stackCapacityAt⟩
#print axioms FrameNewPhysicalSeed.after_upper_frame
end InitECandidate.Runtime

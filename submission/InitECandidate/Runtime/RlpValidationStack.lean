import InitECandidate.Runtime.RlpValidationPushFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Saved parent interval in a validator continuation record. -/
structure RlpValidationFrame where
  record : BitVec 64
  resume : BitVec 64
  stop : BitVec 64

def rlpValidationStackTop : List RlpValidationFrame → BitVec 64
  | [] => 0
  | frame :: _ => frame.record

/-- A finite linked stack with non-wrapping records above a scratch frontier. -/
inductive RlpValidationStack (memory : BitVec 64 → HolWordLab 64) (frontier : Nat) :
    List RlpValidationFrame → Prop where
  | nil : RlpValidationStack memory frontier []
  | cons (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
      (nonzero : frame.record ≠ 0)
      (above : frontier ≤ frame.record.toNat)
      (bounded : frame.record.toNat + 24 ≤ 2^64)
      (resume : memory frame.record = .word frame.resume)
      (stop : memory (frame.record + 8) = .word frame.stop)
      (link : memory (frame.record + 16) = .word (rlpValidationStackTop rest))
      (tail : RlpValidationStack memory frontier rest) :
      RlpValidationStack memory frontier (frame :: rest)

/-- Moving the frontier down leaves the existing linked-stack certificate valid. -/
theorem RlpValidationStack.lower_frontier {memory : BitVec 64 → HolWordLab 64} {frontier lower : Nat}
    {frames : List RlpValidationFrame} (valid : RlpValidationStack memory frontier frames) (below : lower ≤ frontier) :
    RlpValidationStack memory lower frames := by
  induction valid with
  | nil => exact .nil
  | cons frame rest nonzero above bounded resume stop link tail ih =>
    exact .cons frame rest nonzero (by omega) bounded resume stop link ih

/-- A new validator push retains the complete older linked stack. -/
theorem RlpValidationStack.after_push {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch after stop top payload : BitVec 64) {frames : List RlpValidationFrame}
    (valid : RlpValidationStack state.memory scratch.toNat frames) (fits : 24 ≤ scratch.toNat) :
    RlpValidationStack
      (rlpValidationPushPost state (scratchAllocationEnd scratch 24) after stop top payload).memory
      scratch.toNat frames := by
  induction valid with
  | nil => exact .nil
  | cons frame rest nonzero above bounded resume savedStop link tail ih =>
    have preserved := rlpValidation_push_preserves_older_record state scratch after stop top payload frame.record fits above bounded
    refine .cons frame rest nonzero above bounded ?_ ?_ ?_ ih
    · have field := preserved 0 (by decide)
      change (rlpValidationPushPost state (scratchAllocationEnd scratch 24) after stop top payload).memory
        (frame.record + 0#64) = state.memory (frame.record + 0#64) at field
      simpa only [BitVec.add_zero] using field.trans (by simpa only [BitVec.add_zero] using resume)
    · exact (preserved 8 (by decide)).trans savedStop
    · exact (preserved 16 (by decide)).trans link

/-- The checked list-push state extends the linked-stack certificate by its
new continuation record while retaining every previous record. -/
theorem RlpValidationStack.push {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch after stop payload : BitVec 64) {frames : List RlpValidationFrame}
    (valid : RlpValidationStack state.memory scratch.toNat frames) (fits : 24 ≤ scratch.toNat)
    (nonzero : scratchAllocationEnd scratch 24 ≠ 0) :
    let record := scratchAllocationEnd scratch 24
    let post := rlpValidationPushPost state record after stop (rlpValidationStackTop frames) payload
    RlpValidationStack post.memory record.toNat ({record := record,resume := after,stop := stop} :: frames) := by
  have previous := valid.after_push state scratch after stop (rlpValidationStackTop frames) payload fits
  have before := scratchAllocationEnd_before scratch 24 fits
  change (scratchAllocationEnd scratch 24).toNat + 24 ≤ scratch.toNat at before
  have topBound := scratch.isLt
  have below : (scratchAllocationEnd scratch 24).toNat ≤ scratch.toNat := by omega
  have recordBound : (scratchAllocationEnd scratch 24).toNat + 24 ≤ 2^64 := by omega
  have fields := rlpValidation_push_post state (scratchAllocationEnd scratch 24) after stop (rlpValidationStackTop frames) payload
  dsimp only at fields ⊢
  exact .cons _ frames nonzero (Nat.le_refl _) recordBound fields.2.2.2.1 fields.2.2.2.2.1
    fields.2.2.2.2.2.1 (previous.lower_frontier below)

#print axioms RlpValidationStack.push
#print axioms RlpValidationStack.lower_frontier
#print axioms RlpValidationStack.after_push
end InitECandidate.Runtime

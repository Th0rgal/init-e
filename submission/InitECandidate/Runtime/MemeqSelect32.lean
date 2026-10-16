import InitECandidate.Runtime.MemeqReadability
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memeqSizeCondition (size : BitVec 64) : ExpHOL 64 :=
  .cmp .equal (.var .local (ofString "n")) (.const size)

def memeqAfter32 : ProgHOL 64 :=
  match memeqAlignedBody with | .seq _ (.seq _ rest) => rest | _ => .skip

theorem source_memeq_aligned_prefix : memeqAlignedBody =
    .seq (.ite (memeqSizeCondition 20) memeqFast20 .skip)
      (.seq (.ite (memeqSizeCondition 32) memeqFast32 .skip) memeqAfter32) := by rfl

/-- Size32 selects the original unrolled path and its return skips all
remaining generic loops, at any available source clock. -/
theorem evaluate_memeq_aligned32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state memeqAlignedBody =
        (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  have no20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 20) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have yes32 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memeqSizeCondition 32) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [memeqSizeCondition,evalHOLExact,sizeLocal,Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_offsets state a b [0,8,16,24] [] aLocal bLocal domain (by simp)
  have fast : evaluateHOLFiniteState state memeqFast32 =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
    rw [source_memeq_fast32]
    exact run
  refine ⟨value,boolean,?_⟩
  rw [source_memeq_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,no20]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,yes32]
  simp only [show ¬(1 : BitVec 64) = 0 by decide,if_neg,fast]
  rfl

#print axioms source_memeq_aligned_prefix
#print axioms evaluate_memeq_aligned32
end InitECandidate.Runtime

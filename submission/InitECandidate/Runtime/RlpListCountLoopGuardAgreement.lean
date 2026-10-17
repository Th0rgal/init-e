import InitECandidate.Runtime.RlpListCountLoopCountStrict
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpListCount_loop_guard_matches_final_count {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpListCountLoopWitness state pointer length scratch frame ceiling)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : (length.toNat - valid.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock)
    (count : BitVec 64) (atCount : post.locals.lookup (ofString "count") = some (.val (.word count)))
    (run : evaluateHOLFiniteState state rlpListCountLoop = (none,post)) :
    (valid.offset.toNat < length.toNat ↔ valid.count.toNat < count.toNat) := by
  constructor
  · intro enabled
    exact rlpListCount_loop_normal_count_strict state post pointer length scratch frame ceiling inputLimit
      valid noWrap lengthBound limitBound orderedFrame framePositive scratchBelow budget enabled count atCount run
  · intro smaller
    by_contra disabled
    have guard : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = some (.val (.word 0)) := by
      simp [evalHOLFinite,evalHOLExact,valid.offsetLocal,valid.lengthLocal,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,disabled]
    rw [source_rlpListCount_loop,evaluateHOLFiniteState_while_total,guard] at run
    have same : state = post := (Prod.mk.inj run).2
    have equal : valid.count = count := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj
      (valid.countLocal.symm.trans (by rw [same]; exact atCount))))
    rw [equal] at smaller
    omega

#print axioms rlpListCount_loop_guard_matches_final_count
end InitECandidate.Runtime

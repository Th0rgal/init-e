import InitECandidate.Runtime.MerklePaddingBound
import InitECandidate.Runtime.Sha256PairMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def merklePaddingArguments : List (ExpHOL 64) :=
  match merklePaddingBody with | .seq (.call _ _ arguments) _ => arguments | _ => []

theorem source_merklePadding_arguments : merklePaddingBody =
    .seq (.call (some (none,none)) (ofString "sha256_pair") merklePaddingArguments)
      (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"),.const 1])) := by rfl

/-- One original Merkle padding iteration preserves memory below its buffer,
as well as outside the SHA state and accelerator, and advances the real counter. -/
theorem merklePadding_body_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes index watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "d") = some (.val (.word index)))
    (aligned : buf.toNat % 8 = 0)
    (fits : buf.toNat + 32 ≤ 33806089496) (before : watched.toNat < buf.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state merklePaddingBody = (none,post)) :
    post.memory watched = state.memory watched ∧
      post.locals.lookup (ofString "d") = some (.val (.word (index + (1#64)))) := by
  rw [source_merklePadding_arguments,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_pair") merklePaddingArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some stopped => cases run
    | none =>
      have frame := shaPair_call_normal_memory state middle merklePaddingArguments pointer accelerator
        buf buf (zeroHashes + index * (32#64)) watched
        (by simp [merklePaddingArguments,source_merklePadding_body,evalListHOLExact,evalHOLExact,atBuf,atIndex,atZero,
          wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,BitVec.add_assoc]) atPointer atAccel
        accelAligned aligned accelFits pointerFits fits accelOutside pointerOutside
        (Or.inl before) code budget called
      have kept := evaluate_avoidsLocal_flowing (ofString "d")
        (.call (some (none,none)) (ofString "sha256_pair") merklePaddingArguments) rfl state
        (by rw [called]; exact Or.inl rfl)
      have metadata := evaluateHOLFiniteState_metadata state
        (.call (some (none,none)) (ofString "sha256_pair") merklePaddingArguments)
      rw [called] at kept metadata
      have counter := (CountedBody.incr (counter := ofString "d") (step := (1 : BitVec 64))).run middle
        (metadata.1.trans code) index (kept.trans atIndex) (Nat.zero_le _)
      dsimp only at run
      rw [run] at counter
      have memory := evaluate_readOnly_memory
        (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"),.const 1])) rfl middle
      rw [run] at memory
      exact ⟨(congrFun memory watched).trans frame,(counter.2.2.2.2 rfl).1⟩

#print axioms source_merklePadding_arguments
#print axioms merklePadding_body_normal_memory
end InitECandidate.Runtime

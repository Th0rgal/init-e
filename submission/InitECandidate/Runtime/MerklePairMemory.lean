import InitECandidate.Runtime.MerkleLevelBound
import InitECandidate.Runtime.Sha256PairMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def merklePairArguments : List (ExpHOL 64) :=
  match merklePairBody with | .seq (.call _ _ arguments) _ => arguments | _ => []

theorem source_merklePair_arguments : merklePairBody =
    .seq (.call (some (none,none)) (ofString "sha256_pair") merklePairArguments)
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) := by rfl

/-- One original Merkle pair iteration preserves memory below its buffer,
as well as outside the SHA state and accelerator, and advances the real counter. -/
theorem merklePair_body_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf index watched : BitVec 64) (chunks : Nat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (small : index.toNat < chunks) (aligned : buf.toNat % 8 = 0)
    (fits : buf.toNat + chunks * 32 ≤ 33806089496) (before : watched.toNat < buf.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state merklePairBody = (none,post)) :
    post.memory watched = state.memory watched ∧
      post.locals.lookup (ofString "j") = some (.val (.word (index + (1#64)))) := by
  have multiplied : (index * (32#64)).toNat = index.toNat * 32 := by
    apply BitVec.toNat_mul_of_lt
    change index.toNat * 32 < 2 ^ 64
    omega
  have address : (buf + index * (32#64)).toNat = buf.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [multiplied]; omega),multiplied]
  have outputAligned : (buf + index * (32#64)).toNat % 8 = 0 := by
    rw [address,Nat.add_mod,Nat.mul_mod,aligned]; simp
  have outputFits : (buf + index * (32#64)).toNat + 32 ≤ 33806089496 := by rw [address]; omega
  rw [source_merklePair_arguments,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_pair") merklePairArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some stopped => cases run
    | none =>
      have frame := shaPair_call_normal_memory state middle merklePairArguments pointer accelerator
        (buf + index * (32#64)) (buf + index * (64#64)) (buf + index * (64#64) + (32#64)) watched
        (by simp [merklePairArguments,source_merklePair_body,evalListHOLExact,evalHOLExact,atBuf,atIndex,
          wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,BitVec.add_assoc]) atPointer atAccel
        accelAligned outputAligned accelFits pointerFits outputFits accelOutside pointerOutside
        (Or.inl (by rw [address]; omega)) code budget called
      have kept := evaluate_avoidsLocal_flowing (ofString "j")
        (.call (some (none,none)) (ofString "sha256_pair") merklePairArguments) rfl state
        (by rw [called]; exact Or.inl rfl)
      have metadata := evaluateHOLFiniteState_metadata state
        (.call (some (none,none)) (ofString "sha256_pair") merklePairArguments)
      rw [called] at kept metadata
      have counter := (CountedBody.incr (counter := ofString "j") (step := (1 : BitVec 64))).run middle
        (metadata.1.trans code) index (kept.trans atIndex) (Nat.zero_le _)
      dsimp only at run
      rw [run] at counter
      have memory := evaluate_readOnly_memory
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) rfl middle
      rw [run] at memory
      exact ⟨(congrFun memory watched).trans frame,(counter.2.2.2.2 rfl).1⟩

#print axioms source_merklePair_arguments
#print axioms merklePair_body_normal_memory
end InitECandidate.Runtime

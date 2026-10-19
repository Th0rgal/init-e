import InitECandidate.Runtime.MerklePaddingSuffixMemory
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleDepth_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merklePaddingCost + 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 11) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_merkleDepth_declaration] at run
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "d")
    (.var .local (ofString "dn")) initial (merkleizeAt 12) (some (.returned value))
    (by simp [evalHOLExact,atIndex]) run
  let entered := setVarHOLFinite (ofString "d") (.val (.word initial)) state
  have keep (key : MlS) (different : key ≠ ofString "d") : entered.locals.lookup key = state.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have frame := merklePadding_suffix_returned_memory entered inner pointer accelerator buf zeroHashes initial target out mark watched value
    atPointer atAccel atZero ((keep _ (by decide)).trans atBuf)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atTarget) ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small limit aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside code budget bodyRun
  rw [scope]
  exact frame

#print axioms merkleDepth_suffix_returned_memory
end InitECandidate.Runtime

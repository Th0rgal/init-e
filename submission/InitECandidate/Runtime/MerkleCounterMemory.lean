import InitECandidate.Runtime.MerkleTreeSuffixMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleCounter_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark cur watched : BitVec 64) (chunks : Nat) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atCur : state.locals.lookup (ofString "size") = some (.val (.word cur)))
    (countBound : cur.toNat ≤ chunks) (positive : 0 < chunks) (chunksBound : chunks ≤ 134217728)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + chunks * 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merkleInputTreeCost + merklePaddingCost + 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 9) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have source : merkleizeAt 9 = .dec (ofString "cur") .one (.var .local (ofString "size")) (merkleizeAt 10) := by rfl
  rw [source] at run
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "cur")
    (.var .local (ofString "size")) cur (merkleizeAt 10) (some (.returned value))
    (by simp [evalHOLExact,atCur]) run
  let entered := setVarHOLFinite (ofString "cur") (.val (.word cur)) state
  have keep (key : MlS) (different : key ≠ ofString "cur") : entered.locals.lookup key = state.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have frame := merkleTree_suffix_returned_memory entered inner pointer accelerator buf zeroHashes initial target out mark cur watched chunks value
    atPointer atAccel atZero ((keep _ (by decide)).trans atBuf) ((keep _ (by decide)).trans atIndex)
    ((keep _ (by decide)).trans atTarget)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) countBound positive chunksBound
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small limit aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside code budget bodyRun
  rw [scope]
  exact frame

#print axioms merkleCounter_suffix_returned_memory
end InitECandidate.Runtime

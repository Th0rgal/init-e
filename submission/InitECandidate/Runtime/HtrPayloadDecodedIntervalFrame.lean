import InitECandidate.Runtime.HtrNewPayloadPayloadBound
import InitECandidate.Runtime.RlpSliceRecordFrame
import InitECandidate.Runtime.RlpSliceInputPrefixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Only the five payload slice pairs and transaction slice array need to be
framed when carrying decoded hash metadata across the stateless suffix. -/
theorem HtrPayloadDecoded.after_interval_frame {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength : BitVec 64}
    (ctx : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength)
    (payloadFits : payload.toNat + 72 < 2 ^ 64)
    (arrayFits : array.toNat + count.toNat * 16 < 2 ^ 64)
    (domain : post.memaddrs = state.memaddrs)
    (headerFrame : ∀ w : BitVec 64, payload.toNat ≤ w.toNat → w.toNat ≤ payload.toNat + 72 → post.memory w = state.memory w)
    (arrayFrame : ∀ w : BitVec 64, array.toNat ≤ w.toNat → w.toNat < array.toNat + count.toNat * 16 → post.memory w = state.memory w) :
    HtrPayloadDecoded post payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength := by
  have cell (index p n : BitVec 64) (inside : index.toNat ≤ 4) (old : RlpSliceEntry state payload index p n) :
      RlpSliceEntry post payload index p n :=
    old.after_record_frame state post payload index p n inside payloadFits domain headerFrame
  exact ⟨ctx.small,ctx.countBound,cell 2 _ _ (by decide) ctx.transactions,
    ctx.slices.after_interval_frame state post array input inputLength count.toNat arrayFits domain arrayFrame,
    cell 0 _ _ (by decide) ctx.rawEntry,cell 3 _ _ (by decide) ctx.withdrawalEntry,ctx.withdrawalBound,
    cell 4 _ _ (by decide) ctx.requestEntry,ctx.requestBound,cell 1 _ _ (by decide) ctx.blobEntry,ctx.blobBound⟩

#print axioms HtrPayloadDecoded.after_interval_frame
end InitECandidate.Runtime

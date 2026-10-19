import InitECandidate.Runtime.StatelessHashSuffixPayloadDecoded
import InitECandidate.Runtime.StatelessPayloadStoreBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual outer payload-pointer store and hash/request/witness suffix
preserve the complete decoded payload metadata, including an empty tx array. -/
theorem stateless_payload_store_suffix_decoded {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength : BitVec 64)
    (atPayload : t.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (decoded : HtrPayloadDecoded t payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength)
    (scratchBelow : offsets.toNat + 40 ≤ S.toNat) (siBefore : S.toNat + 96 ≤ payload.toNat)
    (payloadHeap : payload.toNat + 72 < H.toNat)
    (arrayAfter : count = 0 ∨ payload.toNat ≤ array.toNat) (arrayHeap : array.toNat + count.toNat * 16 ≤ H.toNat)
    (run : evaluateHOLFiniteState t (statelessAt 23) = (some (.returned v), post)) :
    HtrPayloadDecoded post payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength := by
  rw [source_stateless_payload_store] at run
  unfold statelessPayloadStore at run
  obtain ⟨_,tail⟩ := seqStore_returned_exact t post _ _ _ (S + 0) payload v
    (by simp [evalHOLExact,evalListHOLExact,hsi,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atPayload]) run
  let entry : PanSemStateFiniteExact 64 F := {t with memory := wmem t.memory (S + 0) payload}
  have frame (w : BitVec 64) (lo : payload.toNat ≤ w.toNat) : entry.memory w = t.memory w := by
    have ne : w ≠ S + 0 := by
      intro e
      have same : w.toNat = S.toNat := by simpa using congrArg BitVec.toNat e
      omega
    simp only [entry,wmem,if_neg ne]
  have kept : HtrPayloadDecoded entry payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength :=
    decoded.after_interval_frame (by omega) (by omega) rfl
      (fun w lo _ => frame w lo) (fun w lo hi => by
        rcases arrayAfter with zero | lower
        · subst count; simp at hi; omega
        · exact frame w (by omega))
  exact stateless_hash_suffix_payload_decoded entry post NP NL OVH ORQ P L OW S offsets H v code
    hnp hnlen hovh horq hp hlen howit hsi hg heap hb ha payload array count input inputLength raw rawLength
    withdrawals withdrawalCount requests requestLength blobs blobLength kept scratchBelow siBefore payloadHeap arrayAfter arrayHeap tail

#print axioms stateless_payload_store_suffix_decoded
end InitECandidate.Runtime

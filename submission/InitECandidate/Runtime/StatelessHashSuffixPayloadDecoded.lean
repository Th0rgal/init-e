import InitECandidate.Runtime.StatelessHashRequestWitnessReturned
import InitECandidate.Runtime.HtrPayloadDecodedIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual hash/request/witness suffix preserves the previously decoded
payload header and transaction slices below its entry allocation frontier. -/
theorem stateless_hash_suffix_payload_decoded {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    (decoded : HtrPayloadDecoded t payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength)
    (scratchBelow : offsets.toNat + 40 ≤ S.toNat) (siBefore : S.toNat + 96 ≤ payload.toNat)
    (payloadHeap : payload.toNat + 72 < H.toNat)
    (arrayAfter : payload.toNat ≤ array.toNat) (arrayHeap : array.toNat + count.toNat * 16 ≤ H.toNat)
    (run : evaluateHOLFiniteState t (statelessAt 24) = (some (.returned v), post)) :
    HtrPayloadDecoded post payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength := by
  obtain ⟨_,_,_,frame,_⟩ := stateless_hash_request_witness_returned t post NP NL OVH ORQ P L OW S offsets H v code
    hnp hnlen hovh horq hp hlen howit hsi hg heap hb ha run
  have metadata := evaluateHOLFiniteState_metadata t (statelessAt 24)
  rw [run] at metadata
  have keep (w : BitVec 64) (lo : payload.toNat ≤ w.toNat) (hi : w.toNat < H.toNat) : post.memory w = t.memory w := by
    have sNat (c : BitVec 64) (inside : c.toNat ≤ 80) : (S + c).toNat = S.toNat + c.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    have oNat (k : BitVec 64) (inside : k.toNat < 5) : (offsets + k * 8).toNat = offsets.toNat + k.toNat * 8 := by
      rw [BitVec.toNat_add,BitVec.toNat_mul]; simp; omega
    have neS (c : BitVec 64) (inside : c.toNat ≤ 80) : w ≠ S + c := by
      intro e
      have same := congrArg BitVec.toNat e
      rw [sNat c inside] at same
      omega
    apply frame w hi
    · intro k hk e
      have same := congrArg BitVec.toNat e
      rw [oNat k hk] at same
      omega
    · exact neS 8 (by decide)
    · exact neS 16 (by decide)
    · exact neS 24 (by decide)
    · exact neS 32 (by decide)
    · exact ⟨neS 40 (by decide),neS 48 (by decide),neS 56 (by decide),neS 64 (by decide),neS 72 (by decide),neS 80 (by decide)⟩
  exact decoded.after_interval_frame (by omega) (by omega) metadata.2.1
    (fun w lo hi => keep w lo (by omega)) (fun w lo hi => keep w (by omega) (by omega))

#print axioms stateless_hash_suffix_payload_decoded
end InitECandidate.Runtime

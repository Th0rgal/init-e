import InitECandidate.Runtime.StatelessBodyReturnedRequestsLinked
import InitECandidate.Runtime.StatelessBodyReturnedBlobCount
import InitECandidate.Runtime.StatelessBodyReturnedCells
import InitECandidate.Runtime.HtrNewPayloadHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual full decoder returns every readable outer-header field used
by the new-payload hash, including bounded blob count and linked requests. -/
theorem stateless_body_returned_hash_header {F : Type} (s post : PanSemStateFiniteExact 64 F) (P L offsets H : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → H.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (scratchDom : s.memaddrs (offsets + 0) ∧ s.memaddrs (offsets + 8) ∧ s.memaddrs (offsets + 16) ∧
      s.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 40 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2 ^ 64)
    (small : L.toNat ≤ 134217712)
    (run : evaluateHOLFiniteState s (statelessAt 0) = (some (.returned v), post)) :
    ∃ payload blobs count parentRoot record : BitVec 64,
      HtrNewPayloadHeader post H payload blobs count parentRoot record ∧ HtrRequestsDecoded post record ∧
      H.toNat + 32 < record.toNat := by
  have returned := stateless_body_returned_cells s post P L offsets H v code hp hL hg heap hb ha heapArena scratchDom scratchBelow inputFits run
  obtain ⟨payload,NP,OPL,OVH,ORQ,array,n,nextHeap,growth,alignment,cap,payloadCell,_,_,_,_,blobsCell,_,parentCell,_⟩ := returned.2.2.2
  obtain ⟨count,countBound,countCell⟩ := stateless_body_returned_blob_count s post P L offsets H v code hp hL hg heap hb ha
    heapArena scratchDom scratchBelow inputFits small run
  obtain ⟨record,recordAfter,requestDomain,requestCell,requests⟩ := stateless_body_returned_requests_linked s post P L offsets H v code
    hp hL hg heap hb ha heapArena scratchDom scratchBelow inputFits small run
  have domains (c : BitVec 64) (inside : c.toNat ≤ 24) (aligned : c.toNat % 8 = 0) : post.memaddrs (H + c) := by
    rw [returned.2.2.1]
    have natural : (H + c).toNat = H.toNat + c.toNat := BitVec.toNat_add_of_lt (by omega)
    apply heapArena
    · rw [natural,Nat.add_mod,ha,aligned]
    · rw [natural]; omega
    · rw [natural]; omega
  exact ⟨payload,NP + OVH,count,NP + 8,record,
    ⟨domains 0 (by decide) (by decide),domains 8 (by decide) (by decide),domains 16 (by decide) (by decide),
      domains 24 (by decide) (by decide),requestDomain,payloadCell,blobsCell,countCell,parentCell,requestCell,countBound⟩,
    requests,recordAfter⟩

#print axioms stateless_body_returned_hash_header
end InitECandidate.Runtime

import InitECandidate.Runtime.StatelessBodyReturned
import InitECandidate.Runtime.StatelessPayloadSuffixHashDecodedCells
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual return of the full stateless decoder exports the payload
metadata consumed by the hash bound; its span bounds follow from checked offsets. -/
theorem stateless_body_returned_hash_decoded_cells {F : Type} (s post : PanSemStateFiniteExact 64 F) (P L offsets H : BitVec 64)
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
    ∃ payload array count input inputLength withdrawals withdrawalCount requests requestLength blobs blobLength : BitVec 64,
      H.toNat + 96 ≤ payload.toNat ∧
      HtrPayloadDecoded post payload array count input inputLength input inputLength withdrawals withdrawalCount requests requestLength blobs blobLength := by
  rcases evaluate_stateless_at22 s P L H offsets code hp hL hg heap hb with ⟨E, full, _, _, sc⟩ | ⟨x, h1, h2, _⟩
  · rw [run] at sc
    obtain ⟨geoONP, geoOW, geoOPL, geoOVH, geoORQ, gl1, gl2, gl3, gl4, gl5, gl6, L2, hONP, hOW1, hOW2, hsub, hOPL,
      hOVH1, hOVH2, hORQ⟩ := fullAt22_geometry s P L H offsets E full
    obtain ⟨NP, NL, lnp, lnl, hNP, hNPNL⟩ := fullAt22_span s P L H offsets E full inputFits
    obtain ⟨lp, llen, ecode, edom, _⟩ := fullAt22_locals s P L H offsets E full
    obtain ⟨E8, O0, O1, pre, mid⟩ := full
    obtain ⟨_, _, _, _, e8g, e8d, _, _, _, _, _, e8m, _⟩ := pre
    obtain ⟨_, _, req, _, _, _, X88, OPL', OVH', ORQ', _, _, _, emem, eglob, _, _, _, _, lsi, _, _, _, _, _, _, _⟩ := mid
    have nlEq : NL = geoOW - geoONP := lookup_word_eq E _ _ _ lnl gl6
    cases hE : evaluateHOLFiniteState E (statelessAt 22) with
    | mk r out =>
      rw [hE] at sc
      obtain ⟨r1, _, sm, sg, sd⟩ := sc
      dsimp only at r1 sm sg sd
      subst r1
      have sum := allocationGuard_sum_bound H 96 hb req
      have cov := allocationEnd_covers H 96 sum
      have cov1 : H.toNat + 96 ≤ (allocationEnd H 96).toNat := by have := cov.1; simpa using this
      have H1b := allocationEnd_within_heap H 96 hb req
      have hs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
      have eHeap : E.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd H 96))) := by
        rw [eglob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have eOther : ∀ k, k ≠ ofString "heap_ptr" → E.globals.lookup k = s.globals.lookup k := by
        intro k hk; rw [eglob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, e8g]
      have eOffs : E.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
        rw [eOther _ (Ne.symm hs)]; exact hg
      have ld : E.memaddrs = s.memaddrs := edom
      subst nlEq
      have opl44 : geoOPL.toNat = 44 := by rw [hOPL]; rfl
      have npOVH : NP.toNat + geoOVH.toNat ≤ P.toNat + L.toNat := by rw [hsub] at hNPNL; omega
      have npl : (NP + geoOPL).toNat = NP.toNat + geoOPL.toNat := by rw [BitVec.toNat_add]; omega
      have vml : (geoOVH - geoOPL).toNat = geoOVH.toNat - geoOPL.toNat := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
      have payloadSmall : (geoOVH - geoOPL).toNat ≤ 134217712 := by rw [vml]; omega
      obtain ⟨array,count,withdrawals,balance,extra,decoded⟩ :=
        stateless_payload_suffix_hash_decoded_cells E out NP _ geoOPL geoOVH geoORQ (P + 2) (L - 2) geoOW H offsets
          (allocationEnd H 96) v (ecode.trans code) lnp lnl gl3 gl4 gl5 lp llen gl2 lsi eOffs eHeap H1b cov.2.2
          (fun a cellAligned lo hi => by rw [ld]; exact heapArena a cellAligned (by omega) hi)
          (by rw [ld]; exact scratchDom) scratchBelow cov1 payloadSmall (by rw [npl,vml]; omega) hE
      exact ⟨allocationEnd H 96,array,count,NP + geoOPL,geoOVH - geoOPL,
        NP + geoOPL + withdrawals,(balance - withdrawals) / 44,NP + geoOPL + balance,(geoOVH - geoOPL) - balance,
        NP + geoOPL + 540,extra - 540,cov1,decoded.after_frame sd sm⟩
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)

#print axioms stateless_body_returned_hash_decoded_cells
end InitECandidate.Runtime

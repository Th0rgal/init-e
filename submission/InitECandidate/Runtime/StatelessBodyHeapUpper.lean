import InitECandidate.Runtime.StatelessSuffixHeapUpper
import InitECandidate.Runtime.StatelessBodyFinalHeapCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem decode_stateless_input_returned_heap_upper {F : Type} (s post : PanSemStateFiniteExact 64 F) (P L offsets H : BitVec 64)
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
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_stateless_input) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word Hf)) ∧
      H.toNat≤Hf.toNat ∧Hf.toNat≤H.toNat+16*L.toNat+400 := by
  change evaluateHOLFiniteState s (statelessAt 0)=(some (.returned v),post) at run
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
      obtain ⟨Hf,hfinal,lower,upper⟩:=stateless_payload_suffix_heap_upper E out NP _ geoOPL geoOVH geoORQ (P+2) (L-2) geoOW H offsets
        (allocationEnd H 96) v (ecode.trans code) lnp lnl gl3 gl4 gl5 lp llen gl2 lsi eOffs eHeap H1b cov.2.2
        (fun a cellAligned lo hi=>by rw [ld];exact heapArena a cellAligned (by omega) hi)
        (by rw [ld];exact scratchDom) (by omega) (by rw [npl,vml];omega) hE
      have payloadLength : (geoOVH-geoOPL).toNat≤L.toNat := by rw [vml];omega
      have len2 : (L-2).toNat=L.toNat-2 := by
        rw [BitVec.toNat_sub_of_le (by change (2 : BitVec 64).toNat≤L.toNat;exact L2)]
        rfl
      have witnessLength : ((L-2)-geoOW).toNat≤L.toNat := by
        rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr;rw [len2];omega),len2]
        omega
      have heapUpper : (allocationEnd H 96).toNat<H.toNat+96+8 := by simpa using cov.2.1
      exact ⟨Hf,by rw [sg];exact hfinal,by omega,by omega⟩
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)
#print axioms decode_stateless_input_returned_heap_upper
end InitECandidate.Runtime

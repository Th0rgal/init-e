import InitECandidate.Runtime.StatelessBodyReturned
import InitECandidate.Runtime.StatelessWitness22Decoded
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every returned full decoder supplies the three actual linked witness arrays. -/
theorem stateless_body_returned_witness_arrays {F : Type} (s post : PanSemStateFiniteExact 64 F) (P L offsets H : BitVec 64)
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
    (run : evaluateHOLFiniteState s (statelessAt 0) = (some (.returned v), post)) :
    ∃ OW middle last array count codes codeCount headers headerCount finalHeap : BitVec 64,
      OW.toNat ≤ L.toNat - 2 ∧ 2 ≤ L.toNat ∧ 12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧
      last.toNat ≤ ((L - 2) - OW).toNat ∧ v = .val (.word H) ∧
      WitnessArrayLinked post H 40 48 array count (((P + 2) + OW) + (12#64)) (middle - (12#64)) finalHeap ∧
      WitnessArrayLinked post H 56 64 codes codeCount (((P + 2) + OW) + middle) (last - middle) finalHeap ∧
      WitnessArrayLinked post H 72 80 headers headerCount (((P + 2) + OW) + last) (((L - 2) - OW) - last) finalHeap ∧
      (count = 0 ∨ H.toNat + 88 ≤ array.toNat) ∧ (codeCount = 0 ∨ H.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧ H.toNat + 96 ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) := by
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
      have lenSub : (L - (2#64)).toNat = L.toNat - 2 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact L2)]; rfl
      have pAdd : (P + (2#64)).toNat = P.toNat + 2 := by
        rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
      obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
        stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,finalCap,finalAlign,growth,other,_⟩ :=
        stateless_witness22_decoded E out NP _ geoOPL geoOVH geoORQ (P + 2) (L - 2) geoOW H
          (allocationEnd H 96) offsets v (ecode.trans code) lsi lnp lnl gl3 gl4 gl5 lp llen gl2 eOffs eHeap
          H1b cov.2.2 cov1 (by change (P + (2#64)).toNat + (L - (2#64)).toNat < 2^64; rw [pAdd,lenSub]; omega) (by change geoOW.toNat ≤ (L - (2#64)).toNat; rw [lenSub]; exact hOW2) scratchBelow
          (fun a cellAligned lo hi => by rw [ld]; exact heapArena a cellAligned (by omega) hi)
          (by rw [ld]; exact scratchDom) (by rw [npl,vml]; omega) hE
      refine ⟨geoOW,middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,hOW2,L2,lower,ordered,bound,valueEq,
        stateLinked.after_frame out post _ _ _ _ _ _ _ _ sd sm,
        codesLinked.after_frame out post _ _ _ _ _ _ _ _ sd sm,
        headersLinked.after_frame out post _ _ _ _ _ _ _ _ sd sm,origin,codesOrigin,?_,finalCap,finalAlign,(by omega),(by omega),?_⟩
      · rw [sg]; exact finalBinding
      · intro name different
        rw [sg,other name different]; exact eOther name different
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)

#print axioms stateless_body_returned_witness_arrays
end InitECandidate.Runtime

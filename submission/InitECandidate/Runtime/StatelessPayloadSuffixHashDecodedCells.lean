import InitECandidate.Runtime.StatelessPayloadSuffixReturnedCells
import InitECandidate.Runtime.PayloadDeclarationReturnedHashDecoded
import InitECandidate.Runtime.StatelessPayloadStoreSuffixDecoded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original stateless payload declaration and every remaining decoder
operation export the complete payload hash metadata from actual execution. -/
theorem stateless_payload_suffix_hash_decoded_cells {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OPL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hopl : t.locals.lookup (ofString "o_pl") = some (.val (.word OPL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → H.toNat ≤ a.toNat → a.toNat < 33806089496 → t.memaddrs a)
    (scratchDom : t.memaddrs (offsets + 0) ∧ t.memaddrs (offsets + 8) ∧ t.memaddrs (offsets + 16) ∧
      t.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 40 ≤ S.toNat) (siBelow : S.toNat + 96 ≤ H.toNat)
    (small : (OVH - OPL).toNat ≤ 134217712)
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (statelessAt 22) = (some (.returned v), post)) :
    ∃ array count withdrawals balance extra : BitVec 64,
      HtrPayloadDecoded post H array count (NP + OPL) (OVH - OPL) (NP + OPL) (OVH - OPL)
        (NP + OPL + withdrawals) ((balance - withdrawals) / 44) (NP + OPL + balance) ((OVH - OPL) - balance)
        (NP + OPL + 540) (extra - 540) := by
  have capacity := hb
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) statelessPayloadArguments =
      some [.val (.word (NP + OPL)),.val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,hnp,hopl,hovh,wordOpHOL,wordOp,valueIsWord,valueWord]
  have header (c : BitVec 64) (inside : c.toNat ≤ 40) (cellAligned : c.toNat % 8 = 0) : t.memaddrs (H + c) := by
    by_cases fits : H.toNat + c.toNat < 33806089496
    · apply heapArena
      · rw [BitVec.toNat_add_of_lt (by omega),Nat.add_mod,ha,cellAligned]
      · rw [BitVec.toNat_add_of_lt (by omega)]; omega
      · rw [BitVec.toNat_add_of_lt (by omega)]; exact fits
    · -- A returned allocation necessarily reserves the payload record.
      have cap := ret_payloadDecl_cells t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v code args hg heap hb ha
        heapArena scratchDom (by omega) payloadFits run
      obtain ⟨ready,output,nextHeap,array,count,_,_,_,_,_,_,_,_,_,_,_,_,_,bound,_,growth,_⟩ := cap
      apply heapArena
      · rw [BitVec.toNat_add_of_lt (by omega),Nat.add_mod,ha,cellAligned]
      · rw [BitVec.toNat_add_of_lt (by omega)]; omega
      · rw [BitVec.toNat_add_of_lt (by omega)]; omega
  obtain ⟨array,count,nextHeap,withdrawals,balance,extra,ready,output,tail,locals,installed,domain,decoded,
      nextGlobal,nextBound,nextAligned,growth,arrayHeap,origin,nonHeap,postMemory,_,postDomain⟩ :=
    payload_declaration_returned_hash_decoded t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v args hg heap hb ha
      (by omega) small payloadFits scratchDom.1 scratchDom.2.1 scratchDom.2.2.1 scratchDom.2.2.2
      (header 0 (by decide) (by decide)) (header 8 (by decide) (by decide)) (header 16 (by decide) (by decide)) (header 24 (by decide) (by decide))
      (header 32 (by decide) (by decide)) (header 40 (by decide) (by decide)) code run
  have keep (key : MlS) (different : key ≠ ofString "pl") : ready.locals.lookup key = t.locals.lookup key := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have result := stateless_payload_store_suffix_decoded ready output NP NL OVH ORQ P L OW S offsets nextHeap v (installed.trans code)
    ((keep _ (by decide)).trans hnp) ((keep _ (by decide)).trans hnlen) ((keep _ (by decide)).trans hovh)
    ((keep _ (by decide)).trans horq) ((keep _ (by decide)).trans hp) ((keep _ (by decide)).trans hlen)
    ((keep _ (by decide)).trans howit) ((keep _ (by decide)).trans hsi) ((nonHeap _ (by decide)).trans hg)
    nextGlobal nextBound nextAligned H array count (NP + OPL) (OVH - OPL) (NP + OPL) (OVH - OPL)
    (NP + OPL + withdrawals) ((balance - withdrawals) / 44) (NP + OPL + balance) ((OVH - OPL) - balance)
    (NP + OPL + 540) (extra - 540) (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]) decoded
    scratchBelow siBelow (by omega) (by rcases origin with zero | lower; exact Or.inl zero; exact Or.inr (by omega)) arrayHeap tail
  exact ⟨array,count,withdrawals,balance,extra,result.after_frame postDomain postMemory⟩

#print axioms stateless_payload_suffix_hash_decoded_cells
end InitECandidate.Runtime

import InitECandidate.Runtime.FreshTxTables
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000 in
/-- Transaction entry: from the state before the original `state_fresh_tx()` call, with the block pre-state read
table (pointer at `bs + 72`) aligned below the heap pointer, the call returns into a state where, taking the
post-call heap pointer as `P0` and the post-call globals as the static reference `G0`, the arena globals hold and
both read tables used by `get_pre_state_account_optional` have their real layouts in memory, with the block table's
pointer cell and header outside the transaction table's footprint. -/
theorem freshTx_preState_entry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount SP0 FM : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 380 ≤ s.clock)
    (hFM : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word FM)))
    (hSP : ∃ sp : BitVec 64, s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      FM.toNat ≤ sp.toNat ∧ sp.toNat ≤ SP0.toNat)
    (statics : ∀ n ∈ staticGlobalNames, n ≠ ofString "ts" → ∃ y : BitVec 64, s.globals.lookup n = some (.val (.word y)))
    (KLb Tb KSb SDb Cb USb VSb OSb OPSb Nb : BitVec 64) (bb : Nat)
    (invB : HtabAligned KLb Tb KSb SDb Cb USb VSb OSb OPSb Nb bb s) (tablesB : OrderInv s Cb Nb USb OSb OPSb)
    (cntB : Nb.toNat < Cb.toNat) (cellB : s.memory (B + 72) = .word Tb)
    (belowB : OPSb.toNat + Cb.toNat * 8 ≤ pointer.toNat) (recB : B.toNat + 80 ≤ pointer.toNat) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      post.locals = s.locals ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
      ∃ (P Ta KSa SDa USa VSa OSa OPSa : BitVec 64),
        AW SP0 P FM post.globals post.globals ∧
        post.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
        post.globals.lookup (ofString "bs") = some (.val (.word B)) ∧
        post.memory (pointer + 8) = .word Ta ∧
        HLay P Ta (OPSa + 64#64 * 8#64) 20 SDa 64 0 KSa VSa USa OSa OPSa 6 ∧
        Hdr post.memory Ta 20 SDa 64 0 KSa VSa USa OSa OPSa ∧
        post.memory (B + 72) = .word Tb ∧
        HLay P Tb (OPSb + Cb * 8#64) KLb SDb Cb Nb KSb VSb USb OSb OPSb bb ∧
        Hdr post.memory Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb ∧
        (∀ x : BitVec 64, (x = B + 72 ∨ (Tb.toNat ≤ x.toNat ∧ x.toNat < Tb.toNat + 72)) →
          ¬ Foot P Ta (OPSa + 64#64 * 8#64) x) := by
  obtain ⟨post,run,mem,loc,ma,mb,mc,⟨P,hP,leP,alP,inP⟩,hts,glob,_,_,Ta,KSa,SDa,USa,VSa,OSa,OPSa,taLo,taCell,taInv,
    taTab,⟨P',hP',taHi⟩⟩ :=
    stateFreshTx_call_tables s pointer oldTs B oldCount code heap tsGlobal bsGlobal counterGlobal reservation domain ticks
  rw [hP] at hP'
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hP'
  subst hP'
  have hbs : post.globals.lookup (ofString "bs") = some (.val (.word B)) := by
    rw [glob _ (by decide) (by decide) (by decide)]; exact bsGlobal
  -- the block table survives the call
  have hkB := invB.headerKeys; have kbB := invB.keysBefore; have ubB := invB.usedBefore; have obB := invB.orderBefore
  obtain ⟨invB',tabB'⟩ := invB.keep_block tablesB ma mb mc (fun a lo hi => mem a (by omega))
  have b72 : (B + 72).toNat = B.toNat + 72 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
  have cellB' : post.memory (B + 72) = .word Tb := by rw [mem _ (by rw [b72]; omega)]; exact cellB
  obtain ⟨layA,hdrA,eA⟩ := hlay_of_aligned taInv P (by decide) (by
    have := taInv.headerKeys; have := taInv.keysBefore; have := taInv.usedBefore; have := taInv.orderBefore
    have c64 : (64 : BitVec 64).toNat = 64 := rfl
    rw [c64] at *; omega)
  obtain ⟨layB,hdrB,_⟩ := hlay_of_aligned invB' P cntB (by omega)
  refine ⟨post,run,loc,mc,ma,P,Ta,KSa,SDa,USa,VSa,OSa,OPSa,⟨?_,?_,⟨P,hP,le_refl _,inP,alP⟩,?_⟩,hts,hbs,taCell,
    layA,hdrA,cellB',layB,hdrB,?_⟩
  · rw [glob _ (by decide) (by decide) (by decide)]; exact hFM
  · obtain ⟨sp,hsp,a,b⟩ := hSP
    exact ⟨sp,by rw [glob _ (by decide) (by decide) (by decide)]; exact hsp,a,b⟩
  · intro n hn
    refine ⟨rfl,?_⟩
    by_cases e : n = ofString "ts"
    · subst e; exact ⟨pointer,hts⟩
    · have hh : n ≠ ofString "heap_ptr" := by
        intro e'; subst e'; revert hn; decide
      have hj : n ≠ ofString "journal_n" := by
        intro e'; subst e'; revert hn; decide
      rw [glob n hh e hj]; exact statics n hn e
  · intro x hx hf
    have hx' : x.toNat < pointer.toNat := by
      rcases hx with rfl | ⟨_,h2⟩
      · rw [b72]; omega
      · omega
    rcases hf with ⟨h1,_⟩ | h1 <;> omega

#print axioms freshTx_preState_entry
end InitECandidate.Runtime

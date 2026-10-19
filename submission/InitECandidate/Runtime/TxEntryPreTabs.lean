import InitECandidate.Runtime.PreStateHeap
import InitECandidate.Runtime.TxEntryPreState
/-!
Transaction entry for the two-table invariant: after the original `state_fresh_tx()` call, with the post-call heap
pointer as the arena bound, both read tables are valid against their canonical footprints, in memory and mutually
separated (`PreTabs`), and every word below the pre-call heap pointer outside the block table's region lies outside
both footprints.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The five arrays of an aligned table lie after its header and before the end of its order-position array. -/
theorem aligned_arr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s) :
    ∀ x, ArrOf capacity stride keys values used order orderPos x →
      table.toNat + 72 ≤ x.toNat ∧ x.toNat < orderPos.toNat + capacity.toNat * 8 := by
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore
  rintro x (⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩) <;> omega

set_option maxHeartbeats 4000000 in
/-- Transaction entry for the two-table invariant: from the state before the original `state_fresh_tx()` call, with
the block pre-state read table (pointer at `bs + 72`, cell outside its own region) aligned below the heap pointer,
the call returns into a state with the arena globals at the post-call heap pointer `P` (at least the pre-call one)
and `PreTabs` at `P` for the new transaction read table (cell `ts + 8`) and the block table. -/
theorem freshTx_preTabs {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (belowB : OPSb.toNat + Cb.toNat * 8 ≤ pointer.toNat) (recB : B.toNat + 80 ≤ pointer.toNat)
    (cellOutB : ¬ (Tb.toNat ≤ B.toNat + 72 ∧ B.toNat + 72 < OPSb.toNat + Cb.toNat * 8)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      post.locals = s.locals ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
      ∃ P Ta : BitVec 64, pointer.toNat ≤ P.toNat ∧
        AW SP0 P FM post.globals post.globals ∧
        post.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
        post.globals.lookup (ofString "bs") = some (.val (.word B)) ∧
        PreTabs pointer B Ta Tb
          (fun x => x.toNat < pointer.toNat ∧ ¬ (Tb.toNat ≤ x.toNat ∧ x.toNat < OPSb.toNat + Cb.toNat * 8))
          P post.memory := by
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
  have c64 : (64 : BitVec 64).toNat = 64 := rfl
  obtain ⟨layA,hdrA⟩ := hlay_of_aligned taInv P (tabFoot P Ta OPSa 64) (fun x lo hi => Or.inl ⟨lo,hi⟩)
    (fun x h => Or.inr h) (by decide) (by
    have := taInv.headerKeys; have := taInv.keysBefore; have := taInv.usedBefore; have := taInv.orderBefore
    rw [c64] at *; omega)
  obtain ⟨layB,hdrB⟩ := hlay_of_aligned invB' P (tabFoot P Tb OPSb Cb) (fun x lo hi => Or.inl ⟨lo,hi⟩)
    (fun x h => Or.inr h) cntB (by omega)
  have awP : AW SP0 P FM post.globals post.globals := by
    refine ⟨?_,?_,⟨P,hP,le_refl _,inP,alP⟩,?_⟩
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
  -- arithmetic facts about both table regions
  have aB := aligned_arr invB
  have aA := aligned_arr taInv
  have hkA := taInv.headerKeys; have kbA := taInv.keysBefore; have ubA := taInv.usedBefore
  have obA := taInv.orderBefore; have vbA := taInv.valuesBefore
  have vbB := invB.valuesBefore
  rw [c64] at kbA ubA obA vbA
  have p8 : (pointer + 8).toNat = pointer.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
  let lA : TLay := ⟨20,SDa,64,0,KSa,VSa,USa,OSa,OPSa,6⟩
  let lB : TLay := ⟨KLb,SDb,Cb,Nb,KSb,VSb,USb,OSb,OPSb,bb⟩
  -- every byte of table A lies in [pointer + 72, P); every byte of table B lies below pointer
  have inA : ∀ x, (HdrR Ta x ∨ lA.arr x) → pointer.toNat + 72 ≤ x.toNat ∧ x.toNat < P.toNat := by
    rintro x (⟨lo,hi⟩ | h)
    · omega
    · have := aA x h; rw [c64] at this; omega
  have inB : ∀ x, (HdrR Tb x ∨ lB.arr x) → Tb.toNat ≤ x.toNat ∧ x.toNat < OPSb.toNat + Cb.toNat * 8 := by
    rintro x (⟨lo,hi⟩ | h)
    · omega
    · have := aB x h; omega
  have canA : ∀ x, lA.canon Ta P x → pointer.toNat + 72 ≤ x.toNat := by
    rintro x (h | h | h)
    · exact (inA x (Or.inl h)).1
    · exact (inA x (Or.inr h)).1
    · omega
  have canB : ∀ x, lB.canon Tb P x → x.toNat < pointer.toNat → Tb.toNat ≤ x.toNat ∧
      x.toNat < OPSb.toNat + Cb.toNat * 8 := by
    rintro x (h | h | h) hx
    · exact inB x (Or.inl h)
    · exact inB x (Or.inr h)
    · omega
  refine ⟨post,run,loc,mc,ma,P,Ta,by omega,awP,hts,hbs,lA,lB,
    ⟨taCell,hlay_canon layA (le_refl _),hdrA,fun h => by have := canA _ h; rw [p8] at this; omega⟩,
    ⟨cellB',hlay_canon layB (le_refl _),hdrB,fun h => cellOutB (by rw [← b72]; exact canB _ h (by rw [b72]; omega))⟩,
    ?_,?_,?_⟩
  · intro x hx h
    have := canA x h
    rcases hx with rfl | hx
    · rw [b72] at this; omega
    · have := inB x hx; omega
  · intro x hx h
    rcases hx with rfl | hx
    · rcases h with h | h | h
      · have := inB _ (Or.inl h); rw [p8] at this; omega
      · have := inB _ (Or.inr h); rw [p8] at this; omega
      · have : P.toNat ≤ (pointer + 8).toNat := h
        rw [p8] at this; omega
    · have := inA x hx
      rcases h with h | h | h
      · have := inB x (Or.inl h); omega
      · have := inB x (Or.inr h); omega
      · omega
  · intro x ⟨hx,ho⟩
    refine ⟨fun h => by have := canA x h; omega,fun h => ho (canB x h hx)⟩

#print axioms aligned_arr
#print axioms freshTx_preTabs
end InitECandidate.Runtime

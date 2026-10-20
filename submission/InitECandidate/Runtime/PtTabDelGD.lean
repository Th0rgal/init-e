import InitECandidate.Runtime.PtStorWriteGD
import InitECandidate.Runtime.JDelHeapGD
import InitECandidate.Runtime.HashTableDeleteCallValuesIn
/-!
The actual `htab_del(T, K)` call on a ready table with values in `S` (`TabRV`): memory changes only inside the table's
physical region (every outcome, `del_aqgd_content`), and a normally completing call leaves the table ready with values
in `S` at the current heap pointer, its count kept or decremented (root's `HashTableReady.delete_call_values_in` on the
clock-lifted run).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A ready table has the content invariant, with a free slot. -/
theorem tcont_of_tabRV {D : BitVec 64 → Prop} {B : Bool} {T Hl : BitVec 64} {l : TLay} {S : Set (BitVec 64)}
    {M : Mem} (rv : TabRV D B T l Hl S M) : TCont D B M T l ∧ l.N.toNat < l.C.toNat := by
  obtain ⟨F,s,_,hm,hd,hb,hc,_,_,hT,rd,_⟩ := rv
  obtain ⟨inv,oi,room⟩ := rd.toAligned hT
  exact ⟨⟨F,s,hm,hd,hb,hc,inv,oi⟩,room⟩

#print axioms tcont_of_tabRV

/-- A normally completing actual `htab_del(T, K)` on a ready table with values in `S` leaves it ready with values in
`S` at the current heap pointer, count kept or decremented. -/
theorem delRV_post {F : Type} {D : BitVec 64 → Prop} {B : Bool} (s post : PanSemStateFiniteExact 64 F)
    (T K Hc Hl : BitVec 64) (l : TLay) (S : Set (BitVec 64)) (et ek : ExpHOL 64)
    (hd : s.memaddrs = D) (hb : s.be = B) (code : s.code = originalRuntimeCode)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (rv : TabRV D B T l Hl S s.memory)
    (hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc))) (le : Hl.toNat ≤ Hc.toNat)
    (hHE : Hc.toNat ≤ 33806089496) (al : Hc.toNat % 8 = 0)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (args : evalListHOLFinite (liftClock s (l.C.toNat * 57 + 3))
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek] = some [.val (.word T),.val (.word K)])
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "htab_del") [et,ek]) = (none,post)) :
    ∃ N' : BitVec 64, TabRV D B T ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ Hc S post.memory := by
  obtain ⟨F0,s0,P,hm,hd0,hb0,hc0,hP,hC,hT,rd,vi⟩ := rv
  let s' : PanSemStateFiniteExact 64 F := liftClock s (l.C.toNat * 57 + 3)
  have rd' := rd.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm) (code.trans hc0.symm) hH
    (by have := rd.live.frontier.allocated; omega) hHE al
  have vi' := vi.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm)
  have lift := panPropsEvaluateAddClockEq (.call (some (none,none)) (ofString "htab_del") [et,ek]) s none post
    (l.C.toNat * 57 + 3) ⟨run,by simp⟩
  have lift' : evaluateHOLFiniteState s' (.call (some (none,none)) (ofString "htab_del") [et,ek]) =
      (none,liftClock post (l.C.toNat * 57 + 3)) := lift
  have eK : ∀ o : Nat, o < 52 → (K + BitVec.ofNat 64 o).toNat = K.toNat + o := fun o ho => by
    rw [BitVec.toNat_add]; simp; omega
  have klen : l.KL.toNat ≤ 52 := by rcases sup with h | h | h <;> simp [h]
  obtain ⟨post2,run2,⟨N',_,rdy⟩,vin,_,_,_,_,_,addrs,endian⟩ := rd'.delete_call_values_in s' l.KL T Hc l.KS l.SD l.C
    l.US l.VS l.OS l.OPS l.N K l.b sup et ek args hK
    (fun o ho => by show s.memaddrs _; rw [hd]; exact Dall _ (by rw [eK o (by omega)]; omega))
    (fun o ho => by
      show s.memaddrs _; rw [hd]; refine Dall _ ?_
      rw [panByteAlign_toNat64,eK o (by omega)]
      have := Nat.div_mul_le_self (K.toNat + o) 8; omega)
    (by show l.C.toNat * 57 + 3 ≤ s.clock + (l.C.toNat * 57 + 3); omega) S vi'
  rw [lift'] at run2
  simp only [Prod.mk.injEq,true_and] at run2
  subst run2
  exact ⟨N',F,liftClock post (l.C.toNat * 57 + 3),Hc,rfl,addrs.trans hd,endian.trans hb,rdy.live.arrays.code,
    le_refl _,hC,hT,rdy,vin⟩

#print axioms delRV_post

section dc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- The actual `htab_del(et, ek)` call statement on a table with content: globals unchanged, memory outside the
table's physical region unchanged. -/
theorem aqgd_call_htabDel_frame {LP : GA → Prop} (et ek : ExpHOL 64) (T Kk : BitVec 64) (l : TLay) (M1 : Mem)
    (G1 : GA) (tc : TCont D B M1 T l) (room : l.N.toNat < l.C.toNat) (hwT : ¬ TabPhys T l w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek] =
        some [.val (.word T),.val (.word Kk)]) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ ∀ x, ¬ TabPhys T l x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "htab_del") [et,ek]) := by
  refine aqgd_callSpecD (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (LK [(ofString "key",Kk),(ofString "t",T)] L ∧ M = M0') ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => (∃ N' : BitVec 64, (N' = l.N ∨ N'.toNat + 1 = l.N.toNat) ∧
        TCont D B M' T ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ ∧
        ∀ x, ¬ InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M' x = M0' x) ∧ G' = G0')
    _ _ _ _ _ originalRuntimeCode_hashDelete_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,_⟩
    subst hM
    exact aqgd_fixG (del_aqgd_content Kk tc room hwT)
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_hashDelete_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl⟩,rfl⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨⟨_,_,_,fr⟩,eG⟩
    subst hM hG eG
    exact ⟨lp,rfl,fun x hx => fr x hx⟩

#print axioms aqgd_call_htabDel_frame
end dc

section dr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `htab_del(et, ek)` call statement on a ready table with values in `S`: the frame, and the table still
ready with values in `S` at the heap pointer. -/
theorem aqgd_call_htabDel_rv {LP : GA → Prop} (et ek : ExpHOL 64) (T Kk Hl Hc : BitVec 64) (l : TLay)
    (S : Set (BitVec 64)) (M1 : Mem) (G1 : GA) (rv : TabRV D B T l Hl S M1) (hH1 : HeapIs G1 Hc)
    (hHl : Hl.toNat ≤ Hc.toNat) (hwT : ¬ TabPhys T l w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (hK : Kk.toNat % 8 = 0) (hKE : Kk.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek] =
        some [.val (.word T),.val (.word Kk)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => (LP L ∧ G = G1 ∧ ∀ x, ¬ TabPhys T l x → M x = M1 x) ∧
        ∃ N' : BitVec 64, TabRV D B T ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ Hc S M) RR
      (.call (some (none,none)) (ofString "htab_del") [et,ek]) := by
  obtain ⟨tc,room⟩ := tcont_of_tabRV rv
  refine aqgd_addNormal (aqgd_call_htabDel_frame et ek T Kk l M1 G1 tc room hwT hargs) ?_
  intro F s code dom aw _ ⟨lp,hM,hG⟩ post run
  have hH : HeapIs s.globals Hc := by rw [hG]; exact hH1
  have hf := jws_heap_facts aw.1.1.1 hH
  exact delRV_post s post T Kk Hc Hl l S et ek dom.2.1 dom.2.2 code Dall (by rw [hM]; exact rv) hH hHl hf.2.1
    hf.2.2 sup hK hKE (hargs (liftClock s (l.C.toNat * 57 + 3)) dom.2.1 hM hG lp) run

#print axioms aqgd_call_htabDel_rv
end dr
end InitECandidate.Runtime

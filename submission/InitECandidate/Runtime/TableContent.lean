import InitECandidate.Runtime.HtabOrderInv
import InitECandidate.Runtime.PreStateHeap
/-!
Content invariant of a canonical table (`TCont`): the aligned-table invariant (with the occupancy-count agreement) and
the order invariant, witnessed by a state with the given memory, domain and endianness.  `set_content`: a returned
original `htab_set` keeps it, reusing the aligned-world contract `htabSet_returned_tables` on the same run replayed
with a larger clock.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Content invariant of table `T` with layout `l` in memory `M` (domain `D`, endianness `B`): the aligned-table
invariant (header cells, alignment and ordering, occupancy count agreement) and the order invariant, witnessed by
some state with that memory, domain, endianness and the original code. -/
def TCont (D : BitVec 64 → Prop) (B : Bool) (M : Mem) (T : BitVec 64) (l : TLay) : Prop :=
  ∃ (F : Type) (s : PanSemStateFiniteExact 64 F), s.memory = M ∧ s.memaddrs = D ∧ s.be = B ∧
    s.code = originalRuntimeCode ∧ HtabAligned l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N l.b s ∧
    OrderInv s l.C l.N l.US l.OS l.OPS

theorem TCont.toState {D : BitVec 64 → Prop} {B : Bool} {M : Mem} {T : BitVec 64} {l : TLay}
    (h : TCont D B M T l) {G : Type} (r : PanSemStateFiniteExact 64 G) (hm : r.memory = M) (hd : r.memaddrs = D)
    (hb : r.be = B) (hc : r.code = originalRuntimeCode) :
    HtabAligned l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N l.b r ∧ OrderInv r l.C l.N l.US l.OS l.OPS := by
  obtain ⟨F,s,sm,sd,sb,sc,inv,oi⟩ := h
  exact ⟨inv.transfer (hm.trans sm.symm) (hd.trans sd.symm) (hb.trans sb.symm) (hc.trans sc.symm),
    oi.transfer (hm.trans sm.symm) (hd.trans sd.symm) (hb.trans sb.symm)⟩

theorem TCont.ofState {G : Type} {r : PanSemStateFiniteExact 64 G} {T : BitVec 64} {l : TLay}
    (inv : HtabAligned l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N l.b r) (oi : OrderInv r l.C l.N l.US l.OS l.OPS)
    (hc : r.code = originalRuntimeCode) : TCont r.memaddrs r.be r.memory T l :=
  ⟨G,r,rfl,rfl,rfl,hc,inv,oi⟩

#print axioms TCont.toState

/-- A returned original `htab_set` body run keeps the content invariant (for the header layout it leaves behind):
the aligned-world contract is applied to the same run with a larger clock (`panPropsEvaluateAddClockEq`). -/
theorem set_content {F : Type} (r post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (T Kk V H : BitVec 64)
    (l : TLay) (D : BitVec 64 → Prop) (B : Bool) (hd : r.memaddrs = D) (hb : r.be = B)
    (code : r.code = originalRuntimeCode) (Dfull : ∀ a : BitVec 64, a.toNat % 8 = 0 → a.toNat < 33806089496 → D a)
    (ht : r.locals.lookup (ofString "t") = some (.val (.word T)))
    (hk : r.locals.lookup (ofString "key") = some (.val (.word Kk)))
    (hv : r.locals.lookup (ofString "value") = some (.val (.word V)))
    (hH : r.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (al : H.toNat % 8 = 0)
    (hdrP : T.toNat + 72 ≤ H.toNat) (hi : H.toNat ≤ 33806089496) (tc : TCont D B r.memory T l)
    (room : l.N.toNat < l.C.toNat) (small : l.KL.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState r (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned v),post)) :
    ∃ l' : TLay, l'.KL = l.KL ∧ l'.SD = l.SD ∧
      Hdr post.memory T l'.KL l'.SD l'.C l'.N l'.KS l'.VS l'.US l'.OS l'.OPS ∧ TCont D B post.memory T l' := by
  obtain ⟨inv,oi⟩ := tc.toState r rfl hd hb code
  have run' := panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_htab_set) r _ post
    (setBodyCost l.KL l.C l.N) ⟨run,by simp⟩
  have meta' := evaluateHOLFiniteState_metadata r (sourceFunctionBody Guest.guestFn_htab_set)
  rw [run] at meta'
  obtain ⟨C',KS',US',VS',OS',OPS',N',b',inv2,_,_,_,oi2⟩ := htabSet_returned_tables
    { r with clock := r.clock + setBodyCost l.KL l.C l.N } _ v l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N Kk V H l.b
    (inv.transfer rfl rfl rfl rfl) ht hk hv hH al hdrP hi (fun a a8 _ ahi => by rw [hd]; exact Dfull a a8 ahi)
    (oi.transfer rfl rfl rfl) room small (by simp) run'
  refine ⟨⟨l.KL,l.SD,C',N',KS',VS',US',OS',OPS',b'⟩,rfl,rfl,
    ⟨inv2.cell0,inv2.cell8,inv2.cell16,inv2.cell24,inv2.cell32,inv2.cell40,inv2.cell48,inv2.cell56,inv2.cell64⟩,
    F,{ post with clock := post.clock + setBodyCost l.KL l.C l.N },rfl,
    (by have := meta'.2.1; dsimp only at this; exact this.trans hd),
    (by have := meta'.2.2.1; dsimp only at this; exact this.trans hb),
    (by have := meta'.1; dsimp only at this; exact this.trans code),inv2,oi2⟩

#print axioms set_content
end InitECandidate.Runtime

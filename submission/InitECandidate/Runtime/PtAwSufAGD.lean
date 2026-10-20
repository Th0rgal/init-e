import InitECandidate.Runtime.PtAwCallGD
import InitECandidate.Runtime.PtSufAO4GD
/-!
The accounts-written table side condition `AwR` through drops 99-117: the `create_ether(sender, …)` call keeps it
(`hRce1_aw`, key = the pinned sender pointer `S`), and the four block-output counter stores keep it (`hRbo_aw`: outside
words that are not registry cells, hence off the table's cell and region).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section aw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {J C SKB Bo U Sc : BitVec 64} {n m : Nat} {c T : Fin n → BitVec 64} {Out Excl : BitVec 64 → Prop}
  {ko kd kA kB k16 : Fin n} {e : Fin m → Fin n} {ko' kd' kA' kB' : Fin m} {Ts Bs Taw H0 S Y Ix : BitVec 64}
  {M0 : Mem} {BA IA IS KB Ixb : BitVec 64}

/-- A store to an outside word that is no registry cell keeps the side condition. -/
theorem awR_store {a y : BitVec 64} {M : Mem} {G : GA} (h : AwR Out D B J C SKB Ts Taw M G) (ha : Out a)
    (hc : a ≠ Ts + 16#64) : AwR Out D B J C SKB Ts Taw (fun x => if x = a then .word y else M x) G := by
  obtain ⟨la,Hl,H,hH,⟨rv,hl,cell,sup,sd⟩,sep,oT,cT⟩ := h
  refine ⟨la,Hl,H,hH,⟨tabRV_frame rv (fun x hx => ?_),hl,?_,sup,sd⟩,sep,oT,cT⟩
  · have : x ≠ a := fun e => oT a ha (e ▸ hx)
    simp [this]
  · simp [Ne.symm hc,cell]

theorem hRbo_aw (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k) (hc16 : c k16 = Ts + 16#64) :
    ∀ (k y : BitVec 64) (M : Mem) (G : GA), (k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) →
      AwR Out D B J C SKB Ts Taw M G → AwR Out D B J C SKB Ts Taw (fun x => if x = Bo + k then .word y else M x) G :=
  fun k _ _ _ hk h => awR_store h (hBoC k hk).1.1 (fun e => (hBoC k hk).1.2 k16 (e.trans hc16.symm))

#print axioms awR_store
#print axioms hRbo_aw
/-- The `create_ether(sender, …)` call of drops 99-117 keeps the side condition (key = the pinned sender `S`). -/
theorem hRce1_aw (bk : BalKeep2) (hSal : S.toNat % 8 = 0) (hSE : S.toNat + 52 ≤ 33806089496)
    (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko) (hne : ∀ i, e i ≠ k16) (hkd : e kd' = kd)
    (hkA : e kA' = kA) (hkB : e kB' = kB) (hc16 : c k16 = Ts + 16#64)
    (ne : kd ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko)) (hawWs : KoWsL SP0 FM K Pd NB Taw)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSs S Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧ AwR Out D B J C SKB Ts Taw M G)
      (fun _ M G => AwR Out D B J C SKB Ts Taw M G) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "create_ether") [(.var .local (ofString "sender")),(.rstruct [(.rfield 1 (.var .local (ofString "gra"))),(.rfield 2 (.var .local (ofString "gra"))),(.rfield 3 (.var .local (ofString "gra"))),(.rfield 4 (.var .local (ofString "gra")))])]) :=
  aqgd_liftB bk (by simp [keepsG,balWatched,goodBal2_createEther])
    (aqgd_call_createEther_aw (LP := LPSs S Y Ix) _ _ S
      (fun s lp v ev => by simp [EV,evalHOLExact,lp.2] at ev; exact ev.symm) hSal hSE inj hko hne hkd hkA hkB
      hc16 ne hAB hAo hBo hTs hBs hcA hcB hco hcd p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe hkoWs hawWs jB Dall)

#print axioms hRce1_aw
end aw
end InitECandidate.Runtime

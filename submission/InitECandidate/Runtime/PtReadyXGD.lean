import InitECandidate.Runtime.PtTabSetGD
/-!
Transfer of root's ready-table predicates between states of different foreign-function types: `HashTableReady` and
`HashTableValuesIn` only read memory, the address domain, endianness, the code and (for the frontier) the heap
pointer. The frontier may move to any aligned bounded heap pointer at or above the arrays' end.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section tx
variable {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}

theorem hashOccupancyRead_transfer (used : BitVec 64) (memory : r.memory = s.memory)
    (domain : r.memaddrs = s.memaddrs) (endian : r.be = s.be) :
    hashOccupancyRead r used = hashOccupancyRead s used := by
  funext slot
  unfold hashOccupancyRead panMemLoadByteHOL
  simp only [memory,endian]
  by_cases available : r.memaddrs (panByteAlignHOL (used + slot))
  · have before : s.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
    simp only [if_pos available,if_pos before]
  · have before : ¬s.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
    simp only [if_neg available,if_neg before]

theorem HashTableReady.transferX {KL T K SD C U V O OP N P Q : BitVec 64} {b : Nat}
    (rd : HashTableReady KL T K SD C U V O OP N b P s) (memory : r.memory = s.memory)
    (domain : r.memaddrs = s.memaddrs) (endian : r.be = s.be) (code : r.code = s.code)
    (heap : r.globals.lookup (ofString "heap_ptr") = some (.val (.word Q)))
    (allocated : OP.toNat + C.toNat * 8 ≤ Q.toNat) (bounded : Q.toNat ≤ 33806089496) (aligned : Q.toNat % 8 = 0) :
    HashTableReady KL T K SD C U V O OP N b Q r := by
  have occ := hashOccupancyRead_transfer U memory domain endian
  obtain ⟨⟨a,e,_⟩,vw,rv,lk,ord⟩ := rd
  refine ⟨⟨⟨by rw [code]; exact a.code,a.power,a.keysAligned,a.strideAligned,a.valuesAligned,a.usedAligned,
      a.orderAligned,a.orderPosAligned,a.headerKeys,a.headerValues,a.keysBefore,a.valuesBefore,a.usedBefore,
      a.orderBefore,a.endBound,a.fits,fun x h1 h2 => by rw [domain]; exact a.domain x h1 h2,
      by rw [memory]; exact a.cell0,by rw [memory]; exact a.cell8,by rw [memory]; exact a.cell16,
      by rw [memory]; exact a.cell24,by rw [memory]; exact a.cell32,by rw [memory]; exact a.cell40,
      by rw [memory]; exact a.cell48,by rw [memory]; exact a.cell56,by rw [memory]; exact a.cell64,
      by rw [occ]; exact a.agreement,a.room⟩,
    fun p hp => by rw [memory]; exact e p hp,⟨heap,allocated,bounded,aligned⟩⟩,
    fun sl hs ho => by rw [memory]; exact vw sl hs (by rw [← occ]; exact ho),
    fun sl hs ho => by rw [memory]; exact rv sl hs (by rw [← occ]; exact ho),
    fun sl hs ho => by rw [memory]; exact lk sl hs (by rw [← occ]; exact ho),ord⟩

theorem HashTableValuesIn.transferX {T : BitVec 64} {S : Set (BitVec 64)} (vi : HashTableValuesIn T S s)
    (memory : r.memory = s.memory) (domain : r.memaddrs = s.memaddrs) (endian : r.be = s.be) :
    HashTableValuesIn T S r := by
  intro capacity used values capField usedField valuesField slot inside occupied value cell
  have occ := hashOccupancyRead_transfer used memory domain endian
  rw [memory] at capField usedField valuesField cell
  exact vi capacity used values capField usedField valuesField slot inside (by rw [← occ]; exact occupied) value cell

#print axioms HashTableReady.transferX
#print axioms HashTableValuesIn.transferX
end tx
/-- A safe growth allocation plan ends below the heap end: the relocated order-position array lies below it. -/
theorem growPlan_end (pointer capacity stride : BitVec 64)
    (hcap : capacity.toNat * 16 < 2 ^ 64)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)) :
    (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 ≤ 33806089496 := by
  unfold htabGrowAllocationSizes at safe
  obtain ⟨g1,b1,g2,b2,g3,b3,g4,b4,g5,b5,_⟩ := safe
  have s5 := allocationGuard_sum_bound _ _ b4 g5
  have e2 : (capacity * 2).toNat = capacity.toNat * 2 := by
    rw [BitVec.toNat_mul]; simp; omega
  have e16 : (capacity * 2 * 8).toNat = (capacity * 2).toNat * 8 := by
    rw [BitVec.toNat_mul (capacity * 2),e2]; simp; omega
  unfold htabGrowOrderPos htabGrowOrder htabGrowUsed htabGrowValues
  rw [e16] at s5
  exact s5

#print axioms growPlan_end
/-- The state with `k` more clock ticks. -/
def liftClock {F : Type} (s : PanSemStateFiniteExact 64 F) (k : Nat) : PanSemStateFiniteExact 64 F :=
  { s with clock := s.clock + k }

/-- A normally completing actual `htab_set(T, K, V)` call on a ready table with values in `S` (`V ∈ S`) leaves a
ready table with values in `S` at the exit heap pointer (root's all-plans contract on the clock-lifted run). -/
theorem setRV_post {F : Type} {D : BitVec 64 → Prop} {B : Bool} (s post : PanSemStateFiniteExact 64 F)
    (T K V Hc Hl : BitVec 64) (l : TLay) (S : Set (BitVec 64)) (et ek ev : ExpHOL 64)
    (hd : s.memaddrs = D) (hb : s.be = B) (code : s.code = originalRuntimeCode)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (rv : TabRV D B T l Hl S s.memory)
    (hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc))) (le : Hl.toNat ≤ Hc.toNat)
    (hHE : Hc.toNat ≤ 33806089496) (al : Hc.toNat % 8 = 0)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (sd : l.SD.toNat ≤ 56) (hV : V ∈ S)
    (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (args : evalListHOLFinite (liftClock s (2 ^ 74))
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] =
      some [.val (.word T),.val (.word K),.val (.word V)])
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) = (none,post)) :
    ∃ (l' : TLay) (Hp : BitVec 64), post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hp)) ∧
      TabRV D B T l' Hp S post.memory := by
  obtain ⟨F0,s0,P,hm,hd0,hb0,hc0,hP,hC,hT,rd,vi⟩ := rv
  let s' : PanSemStateFiniteExact 64 F := liftClock s (2 ^ 74)
  have rd' := rd.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm) (code.trans hc0.symm) hH
    (by have := rd.live.frontier.allocated; omega) hHE al
  have vi' := vi.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm)
  have lift := panPropsEvaluateAddClockEq (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) s none post
    (2 ^ 74) ⟨run,by simp⟩
  have lift' : evaluateHOLFiniteState s' (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) =
      (none,liftClock post (2 ^ 74)) := lift
  have eK : ∀ o : Nat, o < 52 → (K + BitVec.ofNat 64 o).toNat = K.toNat + o := fun o ho => by
    rw [BitVec.toNat_add]; simp; omega
  have klen : l.KL.toNat ≤ 52 := by rcases sup with h | h | h <;> simp [h]
  have hcap : l.C.toNat * 16 < 2 ^ 64 := by have := rd.live.arrays.endBound; omega
  have res := rd'.set_call_all_plans_values_in s' l.KL T Hc l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N K V l.b sup S vi' hV sd
    (by show 2 ^ 74 ≤ s.clock + 2 ^ 74; omega)
    (fun safe a _ hi => by
      have := growPlan_end Hc l.C l.SD hcap safe
      show s.memaddrs a; rw [hd]; exact Dall a (by omega))
    et ek ev args hC hK
    (fun o ho => by show s.memaddrs _; rw [hd]; exact Dall _ (by rw [eK o (by omega)]; omega))
    (fun o ho => by
      show s.memaddrs _; rw [hd]; refine Dall _ ?_
      rw [panByteAlign_toNat64,eK o (by omega)]
      have := Nat.div_mul_le_self (K.toNat + o) 8; omega)
  rcases res with ⟨post2,run2,rdy,vin,_,_,_,_,addrs,endian⟩ | ⟨ne,_⟩
  · rw [lift'] at run2
    simp only [Prod.mk.injEq,true_and] at run2
    subst run2
    rcases rdy with ⟨nc,_,rp⟩ | rp
    · exact ⟨⟨l.KL,l.SD,l.C,nc,l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩,Hc,rp.live.frontier.heap,F,liftClock post (2 ^ 74),Hc,rfl,
        addrs.trans hd,endian.trans hb,rp.live.arrays.code,le_refl _,hC,hT,rp,vin⟩
    · refine ⟨⟨l.KL,l.SD,l.C * 2,l.N + 1,Hc,htabGrowValues Hc l.C l.SD,htabGrowUsed Hc l.C l.SD,
        htabGrowOrder Hc l.C l.SD,htabGrowOrderPos Hc l.C l.SD,l.b + 1⟩,_,rp.live.frontier.heap,F,liftClock post (2 ^ 74),_,rfl,
        addrs.trans hd,endian.trans hb,rp.live.arrays.code,le_refl _,?_,hT,rp,vin⟩
      show 1 < (l.C * 2).toNat
      rw [BitVec.toNat_mul]; simp; omega
  · exact absurd (by rw [lift']) ne

#print axioms setRV_post
end InitECandidate.Runtime

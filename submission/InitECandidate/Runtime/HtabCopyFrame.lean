import InitECandidate.Runtime.MemcpyCopyContent
import InitECandidate.Runtime.OriginalHashCopyCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_htabCopy_body : sourceFunctionBody Guest.guestFn_htab_copy =
    (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) (.decCall (ofString "n") .one (ofString "alloc") [(.const 72)] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "n")),(.var .local (ofString "t")),(.const 72)]) (.decCall (ofString "keys") .one (ofString "alloc") [(.panop .mul [(.var .local (ofString "cap")),(.var .local (ofString "stride"))])] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "keys")),(.load .one (hashLocalAddress (ofString "t") 32)),(.panop .mul [(.var .local (ofString "cap")),(.var .local (ofString "stride"))])]) (.seq (.store (hashLocalAddress (ofString "n") 32) (.var .local (ofString "keys"))) (.decCall (ofString "vals") .one (ofString "alloc") [(.panop .mul [(.var .local (ofString "cap")),(.const 8)])] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "vals")),(.load .one (hashLocalAddress (ofString "t") 40)),(.panop .mul [(.var .local (ofString "cap")),(.const 8)])]) (.seq (.store (hashLocalAddress (ofString "n") 40) (.var .local (ofString "vals"))) (.decCall (ofString "used") .one (ofString "alloc") [(.var .local (ofString "cap"))] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "used")),(.load .one (hashLocalAddress (ofString "t") 48)),(.var .local (ofString "cap"))]) (.seq (.store (hashLocalAddress (ofString "n") 48) (.var .local (ofString "used"))) (.decCall (ofString "order") .one (ofString "alloc") [(.panop .mul [(.var .local (ofString "cap")),(.const 8)])] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "order")),(.load .one (hashLocalAddress (ofString "t") 56)),(.panop .mul [(.var .local (ofString "cap")),(.const 8)])]) (.seq (.store (hashLocalAddress (ofString "n") 56) (.var .local (ofString "order"))) (.decCall (ofString "order_pos") .one (ofString "alloc") [(.panop .mul [(.var .local (ofString "cap")),(.const 8)])] (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "order_pos")),(.load .one (hashLocalAddress (ofString "t") 64)),(.panop .mul [(.var .local (ofString "cap")),(.const 8)])]) (.seq (.store (hashLocalAddress (ofString "n") 64) (.var .local (ofString "order_pos"))) (.return (.var .local (ofString "n")))))))))))))))))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_htabCopy_body

theorem byteLoad_congr {F G : Type} (s : PanSemStateFiniteExact 64 F) (r : PanSemStateFiniteExact 64 G) (a b : BitVec 64)
    (low : a.toNat % 8 = b.toNat % 8) (cell : s.memory (panByteAlignHOL a) = r.memory (panByteAlignHOL b))
    (domain : s.memaddrs (panByteAlignHOL a) ↔ r.memaddrs (panByteAlignHOL b)) (endian : s.be = r.be) :
    @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun x => Classical.propDecidable (s.memaddrs x)) s.be a =
      @panMemLoadByteHOL 64 _ r.memory r.memaddrs (fun x => Classical.propDecidable (r.memaddrs x)) r.be b := by
  classical
  unfold panMemLoadByteHOL
  dsimp only
  change (if s.memaddrs (panByteAlignHOL a) then some (panGetByteHOL a (s.memory (panByteAlignHOL a)).1 s.be) else none) =
    (if r.memaddrs (panByteAlignHOL b) then some (panGetByteHOL b (r.memory (panByteAlignHOL b)).1 r.be) else none)
  rw [cell,endian]
  by_cases d : r.memaddrs (panByteAlignHOL b)
  · rw [if_pos (domain.mpr d),if_pos d]
    simp only [panGetByteHOL]
    rw [show (64 / 8 : Nat) = 8 from rfl,low]
  · rw [if_neg (fun h' => d (domain.mp h')),if_neg d]

#print axioms byteLoad_congr

/-- One copy phase: allocate a fresh array, copy the source array into it and
record it in the new header; the tail then runs from the recorded state. -/
theorem htabCopy_phase {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArg : ExpHOL 64)
    (srcOff storeOff : BitVec 64) {tail : ProgHOL 64} {v : ValueHOL 64}
    (T Np p Src N : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (nameT : name ≠ ofString "t") (nameN : name ≠ ofString "n")
    (tL : s.locals.lookup (ofString "t") = some (.val (.word T)))
    (nL : s.locals.lookup (ofString "n") = some (.val (.word Np)))
    (sizeEval : ∀ r : PanSemStateFiniteExact 64 F, (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) →
      @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a)) sizeArg = some (.val (.word N)))
    (srcDomainCell : s.memaddrs (T + srcOff)) (srcCell : s.memory (T + srcOff) = .word Src)
    (pAligned : p.toNat % 8 = 0) (srcAligned : Src.toNat % 8 = 0) (n8 : N.toNat % 8 = 0)
    (pInside : p.toNat ≤ 33806089496) (smallS : Src.toNat + N.toNat ≤ 33806089496) (below : Src.toNat + N.toNat ≤ p.toNat)
    (storeBelow : Np.toNat + storeOff.toNat + 8 ≤ p.toNat) (storeFits : Np.toNat + storeOff.toNat < 2 ^ 64)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → s.memaddrs (Src + BitVec.ofNat 64 k))
    (budget : 2 + (N.toNat / 32 + N.toNat / 8 + 11) ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [sizeArg]
      (.seq (.call (some (none,none)) (ofString "memcpy") [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg])
        (.seq (.store (hashLocalAddress (ofString "n") storeOff) (.var .local name)) tail))) = (some (.returned v),post)) :
    ∃ r inner : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState r tail = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      r.locals.lookup name = some (.val (.word p)) ∧ (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) ∧
      r.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd p N))) ∧
      N ≤ (33806089496 : BitVec 64) - p ∧ (allocationEnd p N).toNat ≤ 33806089496 ∧
      r.memaddrs = s.memaddrs ∧ r.be = s.be ∧ r.code = s.code ∧ s.clock ≤ r.clock + 2 + (N.toNat / 32 + N.toNat / 8 + 11) ∧
      r.memory (Np + storeOff) = .word p ∧
      (∀ k : Nat, k < N.toNat → k % 8 = 0 → r.memory (p + BitVec.ofNat 64 k) = s.memory (Src + BitVec.ofNat 64 k)) ∧
      (∀ w : BitVec 64, w ≠ Np + storeOff → (w.toNat < p.toNat ∨ p.toNat + N.toNat ≤ w.toNat) → r.memory w = s.memory w) := by
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1⟩ := alloc_decCall_returned s post _ sizeArg _ p N v
    (by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,sizeEval s (fun _ _ => rfl)]) code heap (by omega) run
  have pFacts := alloc_step_layout p N pInside q1
  have t1 := (o1 _ (Ne.symm nameT)).trans tL
  have nL1 := (o1 _ (Ne.symm nameN)).trans nL
  obtain ⟨M,copyRun,run2⟩ := seq_returned_of_nonreturning_first (fun v => evaluate_noTopReturn _ rfl r1 v) run1
  have copyArgs : evalListHOLFinite r1 (h := fun a => Classical.propDecidable (r1.memaddrs a))
      [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg] =
        some [.val (.word p),.val (.word Src),.val (.word N)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,eval_header_load r1 _ T srcOff Src t1 (by rw [a1]; exact srcDomainCell) (by rw [m1]; exact srcCell),
      sizeEval r1 o1]
    simp [evalHOLExact,n1]
  obtain ⟨content,frame,ml,ma,mb,mc⟩ := memcpy_call_normal_copy r1 M _ p Src N copyArgs (c1.trans code) pAligned srcAligned n8
    pFacts.2.2 smallS (Or.inr below) (fun k hk ha => by rw [a1]; exact srcDomain k hk ha) copyRun
  have copyCost := evaluate_memcpy_call_bounded r1 _ p Src N copyArgs (c1.trans code) (by omega) (by omega)
  have k1' := k1
  rw [copyRun] at copyCost
  obtain ⟨cc1,_,_⟩ := copyCost
  dsimp only at cc1
  have mG := memcpy_call_normal_globals r1 M _ p Src N copyArgs (c1.trans code) copyRun
  have run3 := store_local_seq_returned M i1 _ storeOff Np p _ (by rw [ml]; exact nL1) (eval_delVar _ _ _ (by rw [ml]; exact n1)) run2
  have sNat : (Np + storeOff).toNat = Np.toNat + storeOff.toNat := BitVec.toNat_add_of_lt storeFits
  refine ⟨_,i1,run3,pm1,pa1,pb1,pc1,by rw [show (sourceWriteWord M (Np + storeOff) p).locals = M.locals from rfl,ml]; exact n1,
    fun k ne => by rw [show (sourceWriteWord M (Np + storeOff) p).locals = M.locals from rfl,ml]; exact o1 k ne,
    by rw [show (sourceWriteWord M (Np + storeOff) p).globals = M.globals from rfl,mG]; exact h1,
    q1,f1,by rw [show (sourceWriteWord M (Np + storeOff) p).memaddrs = M.memaddrs from rfl,ma,a1],
    by rw [show (sourceWriteWord M (Np + storeOff) p).be = M.be from rfl,mb,b1],
    by rw [show (sourceWriteWord M (Np + storeOff) p).code = M.code from rfl,mc,c1],
    by change s.clock ≤ M.clock + 2 + _; omega,
    by simp [sourceWriteWord],?_,?_⟩
  · intro k hk ha
    have kNat : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := word_add_toNat p k (by omega)
    simp only [sourceWriteWord]
    rw [if_neg (word_ne_of_toNat (by rw [kNat,sNat]; omega)),content k hk ha,m1]
  · intro w ne outside
    simp only [sourceWriteWord]
    rw [if_neg ne,frame w outside,m1]

#print axioms htabCopy_phase

def htabCopyCost (capacity stride : BitVec 64) : Nat := 200 + 2 * (capacity.toNat * stride.toNat) + 70 * capacity.toNat

set_option maxHeartbeats 4000000 in
/-- The original table copy from an aligned table below the heap pointer
returns the old heap pointer as an aligned table with the same key length,
stride, capacity and count, the same occupancy and order invariant, and keeps all
memory below the old heap pointer. -/
theorem htabCopy_returned_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (above : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (cap8 : 8 ≤ capacity.toNat) (budget : htabCopyCost capacity stride ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_copy) = (some (.returned v),post)) :
    ∃ keys' used' values' order' orderPos' : BitVec 64, v = .val (.word pointer) ∧
      HtabAligned keyLength pointer keys' stride capacity used' values' order' orderPos' count bits post ∧
      OrderInv post capacity count used' order' orderPos' ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w := by
  unfold htabCopyCost at budget
  have kb := inv.keysBefore; have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have hk := inv.headerKeys; have hv := inv.headerValues
  have capPow : capacity.toNat % 8 = 0 := by
    rw [inv.power]
    have : 3 ≤ bits := by
      by_contra h
      have : bits < 3 := by omega
      have : 2 ^ bits < 2 ^ 3 := Nat.pow_lt_pow_right (by decide) this
      rw [inv.power] at cap8; omega
    rw [show bits = 3 + (bits - 3) by omega,Nat.pow_add]; simp
  have csNat : (capacity * stride).toNat = capacity.toNat * stride.toNat := BitVec.toNat_mul_of_lt (by omega)
  have c8Nat : (capacity * 8).toNat = capacity.toNat * 8 := BitVec.toNat_mul_of_lt (by change _ * 8 < _; omega)
  have csMod : (capacity.toNat * stride.toNat) % 8 = 0 := by rw [Nat.mul_mod,inv.strideAligned,Nat.mul_zero,Nat.zero_mod]
  rw [source_htabCopy_body] at run
  obtain ⟨_,i0,e0,run0,m0,a0,b0,c0⟩ := dec_returned_state run
  rw [eval_header_load state _ table 16 capacity tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16] at e0
  cases e0
  obtain ⟨_,i00,e00,run00,m00,a00,b00,c00⟩ := dec_returned_state run0
  rw [eval_header_load _ _ table 8 stride (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)] at e00
  cases e00
  generalize hS2 : setVarHOLFinite (ofString "stride") (.val (.word stride)) (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state) = S2 at run00
  have s2F : S2.memory = state.memory ∧ S2.memaddrs = state.memaddrs ∧ S2.be = state.be ∧ S2.code = state.code ∧
      S2.clock = state.clock ∧ S2.globals = state.globals := by rw [← hS2]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have s2L : ∀ k, k ≠ ofString "stride" → k ≠ ofString "cap" → S2.locals.lookup k = state.locals.lookup k := by
    intro k n1 n2; rw [← hS2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n1,Ne.symm n2]
  have s2Cap : S2.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [← hS2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have s2Stride : S2.locals.lookup (ofString "stride") = some (.val (.word stride)) := by rw [← hS2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have s2T := (s2L _ (by decide) (by decide)).trans tableLocal
  -- the new header
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1⟩ := alloc_decCall_returned S2 i00 _ (.const 72) _ pointer 72 v
    rfl (s2F.2.2.2.1.trans inv.code) (by rw [s2F.2.2.2.2.2]; exact heap) (by rw [s2F.2.2.2.2.1]; omega) run00
  have p1F := alloc_step_layout pointer 72 pointerInside q1
  generalize hp1 : allocationEnd pointer 72 = p1 at *
  have r1T := (o1 _ (by decide)).trans s2T
  obtain ⟨M0,copy0,run2⟩ := seq_returned_of_nonreturning_first (fun v => evaluate_noTopReturn _ rfl r1 v) run1
  have args0 : evalListHOLFinite r1 (h := fun a => Classical.propDecidable (r1.memaddrs a))
      [(.var .local (ofString "n")),(.var .local (ofString "t")),(.const 72)] =
        some [.val (.word pointer),.val (.word table),.val (.word 72)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,n1,r1T]
  have hdrT : ∀ k : Nat, k ≤ 72 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk' => word_add_toNat table k (by have := keys.isLt; omega)
  obtain ⟨content0,frame0,l0,ad0,be0,co0⟩ := memcpy_call_normal_copy r1 M0 _ pointer table 72 args0
    ((c1.trans s2F.2.2.2.1).trans inv.code) pointerAligned inv.tableAligned (by decide) (by omega) (by change _ + 72 ≤ _; omega)
    (Or.inr (by change _ + 72 ≤ _; omega))
    (fun k hk ha => by
      rw [a1,s2F.2.1]
      exact inv.domain _ (by rw [hdrT k (by change k < 72 at hk; omega)]; have := inv.tableAligned; omega)
        (by rw [hdrT k (by change k < 72 at hk; omega)]; omega) (by rw [hdrT k (by change k < 72 at hk; omega)]; change k < 72 at hk; omega))
    copy0
  have cost0 := evaluate_memcpy_call_bounded r1 _ pointer table 72 args0 ((c1.trans s2F.2.2.2.1).trans inv.code) (by decide)
    (by rw [show (72 : BitVec 64).toNat = 72 from rfl]; omega)
  rw [copy0] at cost0
  obtain ⟨cc0,_,_⟩ := cost0
  dsimp only at cc0
  rw [show (72 : BitVec 64).toNat = 72 from rfl] at cc0
  have g0 := memcpy_call_normal_globals r1 M0 _ pointer table 72 args0 ((c1.trans s2F.2.2.2.1).trans inv.code) copy0
  have p1F' : p1.toNat ≤ 33806089496 := f1
  have p1F : pointer.toNat + 72 ≤ p1.toNat ∧ p1.toNat % 8 = 0 ∧ p1.toNat ≤ 33806089496 := ⟨p1F.1,p1F.2.1,f1⟩
  -- facts of the state after the header copy
  have R0T : M0.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [l0]; exact r1T
  have R0N : M0.locals.lookup (ofString "n") = some (.val (.word pointer)) := by rw [l0]; exact n1
  have R0Cap : M0.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [l0,o1 _ (by decide)]; exact s2Cap
  have R0Stride : M0.locals.lookup (ofString "stride") = some (.val (.word stride)) := by rw [l0,o1 _ (by decide)]; exact s2Stride
  have R0H : M0.globals.lookup (ofString "heap_ptr") = some (.val (.word p1)) := by rw [g0]; exact h1
  have R0A : M0.memaddrs = state.memaddrs := ad0.trans (a1.trans s2F.2.1)
  have R0B : M0.be = state.be := be0.trans (b1.trans s2F.2.2.1)
  have R0C : M0.code = originalRuntimeCode := co0.trans ((c1.trans s2F.2.2.2.1).trans inv.code)
  have R0K : state.clock ≤ M0.clock + 24 := by have := s2F.2.2.2.2.1; omega
  have R0Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → M0.memory w = state.memory w := by
    intro w hw; rw [frame0 w (Or.inl hw),m1,s2F.1]
  have R0Hdr : ∀ k : Nat, k < 72 → k % 8 = 0 → M0.memory (pointer + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
    intro k hk ha; rw [content0 k (by change k < 72; omega) ha,m1,s2F.1]
  have hdrP : ∀ k : Nat, k ≤ 72 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k :=
    fun k hk' => word_add_toNat pointer k (by omega)
  clear content0 frame0 l0 ad0 be0 co0 copy0 g0
  generalize M0 = R0 at *
  -- phase 1: keys
  have R0Dom : ∀ k : Nat, k < (capacity * stride).toNat → k % 8 = 0 → R0.memaddrs (keys + BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [R0A]
    have kNat : (keys + BitVec.ofNat 64 k).toNat = keys.toNat + k := word_add_toNat keys k (by rw [csNat] at hk; omega)
    have := inv.keysAligned
    exact inv.domain _ (by rw [kNat]; omega) (by rw [kNat]; omega) (by rw [kNat]; rw [csNat] at hk; omega)
  obtain ⟨R1,J1,run3,pm2,pa2,pb2,pc2,nm1,ol1,hp1,rq1,rf1,ad1,bd1,cd1,ck1,st1,ct1,fr1⟩ :=
    htabCopy_phase R0 i1 (ofString "keys") (.panop .mul [(.var .local (ofString "cap")),(.var .local (ofString "stride"))]) 32 32 table pointer p1 keys (capacity * stride) R0C R0H (by decide) (by decide)
      R0T R0N
      (fun r hr => by simp [evalHOLExact,evalListHOLExact,hr _ (show ofString "cap" ≠ ofString "keys" by decide),
        hr _ (show ofString "stride" ≠ ofString "keys" by decide),R0Cap,R0Stride,panOpHOL,valueIsWord,valueWord])
      (by rw [R0A]; exact inv.header_domain 32 (by omega) (by omega))
      (by rw [R0Below _ (by rw [show (table + 32 : BitVec 64).toNat = table.toNat + 32 from hdrT 32 (by omega)]; omega)]; exact inv.cell32)
      p1F.2.1 inv.keysAligned (by rw [csNat]; omega) p1F.2.2 (by rw [csNat]; omega) (by rw [csNat]; omega)
      (by change pointer.toNat + 32 + 8 ≤ _; omega) (by change pointer.toNat + 32 < _; omega)
      R0Dom (by rw [csNat]; omega) run2
  have p2L := alloc_step_layout p1 (capacity * stride) p1F.2.2 rq1
  generalize hp2 : allocationEnd p1 (capacity * stride) = p2 at *
  have p2F : p1.toNat + (capacity * stride).toNat ≤ p2.toNat ∧ p2.toNat % 8 = 0 ∧ p2.toNat ≤ 33806089496 := ⟨p2L.1,p2L.2.1,rf1⟩
  rw [csNat] at p2F
  have R1T : R1.locals.lookup (ofString "t") = some (.val (.word table)) := (ol1 _ (by decide)).trans R0T
  have R1N : R1.locals.lookup (ofString "n") = some (.val (.word pointer)) := (ol1 _ (by decide)).trans R0N
  have R1Cap : R1.locals.lookup (ofString "cap") = some (.val (.word capacity)) := (ol1 _ (by decide)).trans R0Cap
  have R1Stride : R1.locals.lookup (ofString "stride") = some (.val (.word stride)) := (ol1 _ (by decide)).trans R0Stride
  have R1H := hp1
  have R1A : R1.memaddrs = state.memaddrs := ad1.trans R0A
  have R1B : R1.be = state.be := bd1.trans R0B
  have R1C : R1.code = originalRuntimeCode := cd1.trans R0C
  rw [csNat] at ck1
  have R1Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → R1.memory w = state.memory w := by
    intro w hw
    rw [fr1 w (word_ne_of_toNat (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega))
      (Or.inl (by omega)),R0Below w hw]
  -- phase 2: vals
  have R1Dom : ∀ k : Nat, k < (capacity * 8).toNat → k % 8 = 0 → R1.memaddrs (values + BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [R1A]
    have kNat : (values + BitVec.ofNat 64 k).toNat = values.toNat + k := word_add_toNat values k (by rw [c8Nat] at hk; omega)
    have := inv.valuesAligned
    exact inv.domain _ (by rw [kNat]; omega) (by rw [kNat]; omega) (by rw [kNat]; rw [c8Nat] at hk; omega)
  obtain ⟨R2,J2,run4,pm3,pa3,pb3,pc3,nm2,ol2,hp2,rq2,rf2,ad2,bd2,cd2,ck2,st2,ct2,fr2⟩ :=
    htabCopy_phase R1 J1 (ofString "vals") (.panop .mul [(.var .local (ofString "cap")),(.const 8)]) 40 40 table pointer p2 values (capacity * 8) R1C R1H (by decide) (by decide)
      R1T R1N
      (fun r hr => by simp [evalHOLExact,evalListHOLExact,hr _ (show ofString "cap" ≠ ofString "vals" by decide),
        hr _ (show ofString "stride" ≠ ofString "vals" by decide),R1Cap,R1Stride,panOpHOL,valueIsWord,valueWord])
      (by rw [R1A]; exact inv.header_domain 40 (by omega) (by omega))
      (by rw [R1Below _ (by rw [show (table + 40 : BitVec 64).toNat = table.toNat + 40 from hdrT 40 (by omega)]; omega)]; exact inv.cell40)
      p2F.2.1 inv.valuesAligned (by rw [c8Nat]; omega) p2F.2.2 (by rw [c8Nat]; omega) (by rw [c8Nat]; omega)
      (by change pointer.toNat + 40 + 8 ≤ _; omega) (by change pointer.toNat + 40 < _; omega)
      R1Dom (by rw [c8Nat]; omega) run3
  have p3L := alloc_step_layout p2 (capacity * 8) p2F.2.2 rq2
  generalize hp3 : allocationEnd p2 (capacity * 8) = p3 at *
  have p3F : p2.toNat + (capacity * 8).toNat ≤ p3.toNat ∧ p3.toNat % 8 = 0 ∧ p3.toNat ≤ 33806089496 := ⟨p3L.1,p3L.2.1,rf2⟩
  rw [c8Nat] at p3F
  have R2T : R2.locals.lookup (ofString "t") = some (.val (.word table)) := (ol2 _ (by decide)).trans R1T
  have R2N : R2.locals.lookup (ofString "n") = some (.val (.word pointer)) := (ol2 _ (by decide)).trans R1N
  have R2Cap : R2.locals.lookup (ofString "cap") = some (.val (.word capacity)) := (ol2 _ (by decide)).trans R1Cap
  have R2Stride : R2.locals.lookup (ofString "stride") = some (.val (.word stride)) := (ol2 _ (by decide)).trans R1Stride
  have R2H := hp2
  have R2A : R2.memaddrs = state.memaddrs := ad2.trans R1A
  have R2B : R2.be = state.be := bd2.trans R1B
  have R2C : R2.code = originalRuntimeCode := cd2.trans R1C
  rw [c8Nat] at ck2
  have R2Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → R2.memory w = state.memory w := by
    intro w hw
    rw [fr2 w (word_ne_of_toNat (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega))
      (Or.inl (by omega)),R1Below w hw]
  -- phase 3: used
  have R2Dom : ∀ k : Nat, k < (capacity).toNat → k % 8 = 0 → R2.memaddrs (used + BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [R2A]
    have kNat : (used + BitVec.ofNat 64 k).toNat = used.toNat + k := word_add_toNat used k (by omega)
    have := inv.usedAligned
    exact inv.domain _ (by rw [kNat]; omega) (by rw [kNat]; omega) (by rw [kNat]; omega)
  obtain ⟨R3,J3,run5,pm4,pa4,pb4,pc4,nm3,ol3,hp3,rq3,rf3,ad3,bd3,cd3,ck3,st3,ct3,fr3⟩ :=
    htabCopy_phase R2 J2 (ofString "used") (.var .local (ofString "cap")) 48 48 table pointer p3 used (capacity) R2C R2H (by decide) (by decide)
      R2T R2N
      (fun r hr => by simp [evalHOLExact,evalListHOLExact,hr _ (show ofString "cap" ≠ ofString "used" by decide),
        hr _ (show ofString "stride" ≠ ofString "used" by decide),R2Cap,R2Stride,panOpHOL,valueIsWord,valueWord])
      (by rw [R2A]; exact inv.header_domain 48 (by omega) (by omega))
      (by rw [R2Below _ (by rw [show (table + 48 : BitVec 64).toNat = table.toNat + 48 from hdrT 48 (by omega)]; omega)]; exact inv.cell48)
      p3F.2.1 inv.usedAligned (by omega) p3F.2.2 (by omega) (by omega)
      (by change pointer.toNat + 48 + 8 ≤ _; omega) (by change pointer.toNat + 48 < _; omega)
      R2Dom (by omega) run4
  have p4L := alloc_step_layout p3 (capacity) p3F.2.2 rq3
  generalize hp4 : allocationEnd p3 (capacity) = p4 at *
  have p4F : p3.toNat + (capacity).toNat ≤ p4.toNat ∧ p4.toNat % 8 = 0 ∧ p4.toNat ≤ 33806089496 := ⟨p4L.1,p4L.2.1,rf3⟩
  have R3T : R3.locals.lookup (ofString "t") = some (.val (.word table)) := (ol3 _ (by decide)).trans R2T
  have R3N : R3.locals.lookup (ofString "n") = some (.val (.word pointer)) := (ol3 _ (by decide)).trans R2N
  have R3Cap : R3.locals.lookup (ofString "cap") = some (.val (.word capacity)) := (ol3 _ (by decide)).trans R2Cap
  have R3Stride : R3.locals.lookup (ofString "stride") = some (.val (.word stride)) := (ol3 _ (by decide)).trans R2Stride
  have R3H := hp3
  have R3A : R3.memaddrs = state.memaddrs := ad3.trans R2A
  have R3B : R3.be = state.be := bd3.trans R2B
  have R3C : R3.code = originalRuntimeCode := cd3.trans R2C
  have R3Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → R3.memory w = state.memory w := by
    intro w hw
    rw [fr3 w (word_ne_of_toNat (by rw [show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega))
      (Or.inl (by omega)),R2Below w hw]
  -- phase 4: order
  have R3Dom : ∀ k : Nat, k < (capacity * 8).toNat → k % 8 = 0 → R3.memaddrs (order + BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [R3A]
    have kNat : (order + BitVec.ofNat 64 k).toNat = order.toNat + k := word_add_toNat order k (by rw [c8Nat] at hk; omega)
    have := inv.orderAligned
    exact inv.domain _ (by rw [kNat]; omega) (by rw [kNat]; omega) (by rw [kNat]; rw [c8Nat] at hk; omega)
  obtain ⟨R4,J4,run6,pm5,pa5,pb5,pc5,nm4,ol4,hp4,rq4,rf4,ad4,bd4,cd4,ck4,st4,ct4,fr4⟩ :=
    htabCopy_phase R3 J3 (ofString "order") (.panop .mul [(.var .local (ofString "cap")),(.const 8)]) 56 56 table pointer p4 order (capacity * 8) R3C R3H (by decide) (by decide)
      R3T R3N
      (fun r hr => by simp [evalHOLExact,evalListHOLExact,hr _ (show ofString "cap" ≠ ofString "order" by decide),
        hr _ (show ofString "stride" ≠ ofString "order" by decide),R3Cap,R3Stride,panOpHOL,valueIsWord,valueWord])
      (by rw [R3A]; exact inv.header_domain 56 (by omega) (by omega))
      (by rw [R3Below _ (by rw [show (table + 56 : BitVec 64).toNat = table.toNat + 56 from hdrT 56 (by omega)]; omega)]; exact inv.cell56)
      p4F.2.1 inv.orderAligned (by rw [c8Nat]; omega) p4F.2.2 (by rw [c8Nat]; omega) (by rw [c8Nat]; omega)
      (by change pointer.toNat + 56 + 8 ≤ _; omega) (by change pointer.toNat + 56 < _; omega)
      R3Dom (by rw [c8Nat]; omega) run5
  have p5L := alloc_step_layout p4 (capacity * 8) p4F.2.2 rq4
  generalize hp5 : allocationEnd p4 (capacity * 8) = p5 at *
  have p5F : p4.toNat + (capacity * 8).toNat ≤ p5.toNat ∧ p5.toNat % 8 = 0 ∧ p5.toNat ≤ 33806089496 := ⟨p5L.1,p5L.2.1,rf4⟩
  rw [c8Nat] at p5F
  have R4T : R4.locals.lookup (ofString "t") = some (.val (.word table)) := (ol4 _ (by decide)).trans R3T
  have R4N : R4.locals.lookup (ofString "n") = some (.val (.word pointer)) := (ol4 _ (by decide)).trans R3N
  have R4Cap : R4.locals.lookup (ofString "cap") = some (.val (.word capacity)) := (ol4 _ (by decide)).trans R3Cap
  have R4Stride : R4.locals.lookup (ofString "stride") = some (.val (.word stride)) := (ol4 _ (by decide)).trans R3Stride
  have R4H := hp4
  have R4A : R4.memaddrs = state.memaddrs := ad4.trans R3A
  have R4B : R4.be = state.be := bd4.trans R3B
  have R4C : R4.code = originalRuntimeCode := cd4.trans R3C
  rw [c8Nat] at ck4
  have R4Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → R4.memory w = state.memory w := by
    intro w hw
    rw [fr4 w (word_ne_of_toNat (by rw [show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega))
      (Or.inl (by omega)),R3Below w hw]
  -- phase 5: order_pos
  have R4Dom : ∀ k : Nat, k < (capacity * 8).toNat → k % 8 = 0 → R4.memaddrs (orderPos + BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [R4A]
    have kNat : (orderPos + BitVec.ofNat 64 k).toNat = orderPos.toNat + k := word_add_toNat orderPos k (by rw [c8Nat] at hk; omega)
    have := inv.orderPosAligned
    exact inv.domain _ (by rw [kNat]; omega) (by rw [kNat]; omega) (by rw [kNat]; rw [c8Nat] at hk; omega)
  obtain ⟨R5,J5,run7,pm6,pa6,pb6,pc6,nm5,ol5,hp5,rq5,rf5,ad5,bd5,cd5,ck5,st5,ct5,fr5⟩ :=
    htabCopy_phase R4 J4 (ofString "order_pos") (.panop .mul [(.var .local (ofString "cap")),(.const 8)]) 64 64 table pointer p5 orderPos (capacity * 8) R4C R4H (by decide) (by decide)
      R4T R4N
      (fun r hr => by simp [evalHOLExact,evalListHOLExact,hr _ (show ofString "cap" ≠ ofString "order_pos" by decide),
        hr _ (show ofString "stride" ≠ ofString "order_pos" by decide),R4Cap,R4Stride,panOpHOL,valueIsWord,valueWord])
      (by rw [R4A]; exact inv.header_domain 64 (by omega) (by omega))
      (by rw [R4Below _ (by rw [show (table + 64 : BitVec 64).toNat = table.toNat + 64 from hdrT 64 (by omega)]; omega)]; exact inv.cell64)
      p5F.2.1 inv.orderPosAligned (by rw [c8Nat]; omega) p5F.2.2 (by rw [c8Nat]; omega) (by rw [c8Nat]; omega)
      (by change pointer.toNat + 64 + 8 ≤ _; omega) (by change pointer.toNat + 64 < _; omega)
      R4Dom (by rw [c8Nat]; omega) run6
  have p6L := alloc_step_layout p5 (capacity * 8) p5F.2.2 rq5
  generalize hp6 : allocationEnd p5 (capacity * 8) = p6 at *
  have p6F : p5.toNat + (capacity * 8).toNat ≤ p6.toNat ∧ p6.toNat % 8 = 0 ∧ p6.toNat ≤ 33806089496 := ⟨p6L.1,p6L.2.1,rf5⟩
  rw [c8Nat] at p6F
  have R5T : R5.locals.lookup (ofString "t") = some (.val (.word table)) := (ol5 _ (by decide)).trans R4T
  have R5N : R5.locals.lookup (ofString "n") = some (.val (.word pointer)) := (ol5 _ (by decide)).trans R4N
  have R5Cap : R5.locals.lookup (ofString "cap") = some (.val (.word capacity)) := (ol5 _ (by decide)).trans R4Cap
  have R5Stride : R5.locals.lookup (ofString "stride") = some (.val (.word stride)) := (ol5 _ (by decide)).trans R4Stride
  have R5H := hp5
  have R5A : R5.memaddrs = state.memaddrs := ad5.trans R4A
  have R5B : R5.be = state.be := bd5.trans R4B
  have R5C : R5.code = originalRuntimeCode := cd5.trans R4C
  rw [c8Nat] at ck5
  have R5Below : ∀ w : BitVec 64, w.toNat < pointer.toNat → R5.memory w = state.memory w := by
    intro w hw
    rw [fr5 w (word_ne_of_toNat (by rw [show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega))
      (Or.inl (by omega)),R4Below w hw]
  have value := return_local_word R5 J5 (ofString "n") pointer v R5N run7
  obtain ⟨rm,ra,rb,rc⟩ := return_local_state R5 J5 (ofString "n") pointer v R5N run7
  have postMem : post.memory = R5.memory :=
    m0.trans (m00.trans (pm1.trans (pm2.trans (pm3.trans (pm4.trans (pm5.trans (pm6.trans rm)))))))
  have postAddr : post.memaddrs = state.memaddrs :=
    a0.trans (a00.trans (pa1.trans (pa2.trans (pa3.trans (pa4.trans (pa5.trans (pa6.trans (ra.trans R5A))))))))
  have postBe : post.be = state.be :=
    b0.trans (b00.trans (pb1.trans (pb2.trans (pb3.trans (pb4.trans (pb5.trans (pb6.trans (rb.trans R5B))))))))
  have postCode : post.code = originalRuntimeCode :=
    c0.trans (c00.trans (pc1.trans (pc2.trans (pc3.trans (pc4.trans (pc5.trans (pc6.trans (rc.trans R5C))))))))
  have word : ∀ k : Nat, k < 2 ^ 64 → (BitVec.ofNat 64 k).toNat = k := fun k hk => by
    change k % 2 ^ 64 = k; exact Nat.mod_eq_of_lt hk
  -- copied occupancy words
  have usedCopy : ∀ k : Nat, k < capacity.toNat → k % 8 = 0 →
      post.memory (p3 + BitVec.ofNat 64 k) = state.memory (used + BitVec.ofNat 64 k) := by
    intro k hk ha
    have kNat : (p3 + BitVec.ofNat 64 k).toNat = p3.toNat + k := word_add_toNat p3 k (by omega)
    rw [postMem,fr5 _ (word_ne_of_toNat (by rw [kNat,show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega))
        (Or.inl (by rw [kNat]; omega)),
      fr4 _ (word_ne_of_toNat (by rw [kNat,show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega))
        (Or.inl (by rw [kNat]; omega)),ct3 k hk ha,R2Below _ (by rw [word_add_toNat used k (by omega)]; omega)]
  have reads : ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead post p3 q = hashOccupancyRead state used q := by
    intro q inside
    unfold hashOccupancyRead
    have pq : (p3 + q).toNat = p3.toNat + q.toNat := BitVec.toNat_add_of_lt (by omega)
    have uq : (used + q).toNat = used.toNat + q.toNat := BitVec.toNat_add_of_lt (by omega)
    have ua := inv.usedAligned
    have e1 : panByteAlignHOL (p3 + q) = p3 + BitVec.ofNat 64 (q.toNat / 8 * 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [byteAlign_toNat,pq,word_add_toNat p3 _ (by omega)]
      omega
    have e2 : panByteAlignHOL (used + q) = used + BitVec.ofNat 64 (q.toNat / 8 * 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [byteAlign_toNat,uq,word_add_toNat used _ (by omega)]
      omega
    apply byteLoad_congr post state (p3 + q) (used + q) (by rw [pq,uq]; omega)
    · rw [e1,e2]; exact usedCopy _ (by omega) (by omega)
    · rw [postAddr]
      constructor
      · intro _
        rw [e2]
        have := word_add_toNat used (q.toNat / 8 * 8) (by omega)
        exact inv.domain _ (by rw [this]; omega) (by rw [this]; omega) (by rw [this]; omega)
      · intro _
        rw [e1]
        have := word_add_toNat p3 (q.toNat / 8 * 8) (by omega)
        exact arena _ (by rw [this]; omega) (by rw [this]; omega) (by rw [this]; omega)
    · exact postBe
  have inv' : HtabAligned keyLength pointer p1 stride capacity p3 p2 p4 p5 count bits post := {
    code := postCode
    power := inv.power
    tableAligned := pointerAligned
    keysAligned := p1F.2.1
    strideAligned := inv.strideAligned
    valuesAligned := p2F.2.1
    usedAligned := p3F.2.1
    orderAligned := p4F.2.1
    orderPosAligned := p5F.2.1
    headerKeys := p1F.1
    headerValues := by omega
    keysBefore := by omega
    valuesBefore := by omega
    usedBefore := by omega
    orderBefore := by omega
    endBound := by omega
    fits := inv.fits
    domain := fun a h1' h2' h3' => by rw [postAddr]; exact arena a h1' h2' (by omega)
    cell0 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega)]; omega)),fr2 _ (word_ne_of_toNat (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega),show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega)]; omega)),fr1 _ (word_ne_of_toNat (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega),show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 from hdrP 0 (by omega)]; omega)),show (pointer + 0 : BitVec 64) = pointer + BitVec.ofNat 64 0 from rfl,R0Hdr 0 (by omega) (by omega)]; exact inv.cell0
    cell8 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega)]; omega)),fr2 _ (word_ne_of_toNat (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega),show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega)]; omega)),fr1 _ (word_ne_of_toNat (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega),show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 from hdrP 8 (by omega)]; omega)),show (pointer + 8 : BitVec 64) = pointer + BitVec.ofNat 64 8 from rfl,R0Hdr 8 (by omega) (by omega)]; exact inv.cell8
    cell16 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega)]; omega)),fr2 _ (word_ne_of_toNat (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega),show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega)]; omega)),fr1 _ (word_ne_of_toNat (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega),show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 from hdrP 16 (by omega)]; omega)),show (pointer + 16 : BitVec 64) = pointer + BitVec.ofNat 64 16 from rfl,R0Hdr 16 (by omega) (by omega)]; exact inv.cell16
    cell24 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega)]; omega)),fr2 _ (word_ne_of_toNat (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega),show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega)]; omega)),fr1 _ (word_ne_of_toNat (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega),show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 from hdrP 24 (by omega)]; omega)),show (pointer + 24 : BitVec 64) = pointer + BitVec.ofNat 64 24 from rfl,R0Hdr 24 (by omega) (by omega)]; exact inv.cell24
    cell32 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega)),fr2 _ (word_ne_of_toNat (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega),show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 from hdrP 32 (by omega)]; omega))]; exact st1
    cell40 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega)),fr3 _ (word_ne_of_toNat (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega),show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 from hdrP 40 (by omega)]; omega))]; exact st2
    cell48 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega)),fr4 _ (word_ne_of_toNat (by rw [show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega),show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 from hdrP 48 (by omega)]; omega))]; exact st3
    cell56 := by rw [postMem,fr5 _ (word_ne_of_toNat (by rw [show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega),show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega)) (Or.inl (by rw [show (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 from hdrP 56 (by omega)]; omega))]; exact st4
    cell64 := by rw [postMem]; exact st5
    agreement := by
      rw [inv.agreement]
      exact (hashOccupiedCount_congr capacity _ _ reads).symm }
  have slot8 : ∀ (B q : BitVec 64), B.toNat + q.toNat * 8 < 2 ^ 64 → B + q * 8 = B + BitVec.ofNat 64 (q.toNat * 8) := by
    intro B q fit
    apply BitVec.eq_of_toNat_eq
    rw [word_mul_add_toNat B q 8 (by change _ + _ * 8 < _; omega),word_add_toNat B _ (by omega)]
    rfl
  refine ⟨p1,p3,p2,p4,p5,value,inv',⟨fun q inside occupied => ?_,fun k inside => ?_⟩,postAddr,postBe,
    fun w hw => by rw [postMem]; exact R5Below w hw⟩
  · obtain ⟨y,hy,ylt⟩ := tables.1 q inside (by rw [← reads q inside]; exact occupied)
    refine ⟨y,?_,ylt⟩
    rw [slot8 p5 q (by omega),postMem,ct5 _ (by rw [c8Nat]; omega) (by omega),
      R4Below _ (by rw [word_add_toNat orderPos _ (by omega)]; omega),← slot8 orderPos q (by omega)]
    exact hy
  · have countLe : count.toNat ≤ capacity.toNat := by
      rw [inv.agreement]; unfold hashOccupiedCount; exact (List.countP_le_length).trans (by simp)
    obtain ⟨x,hx,xlt⟩ := tables.2 k inside
    refine ⟨x,?_,xlt⟩
    have kNat : (p4 + BitVec.ofNat 64 (k.toNat * 8)).toNat = p4.toNat + k.toNat * 8 := word_add_toNat p4 _ (by omega)
    rw [slot8 p4 k (by omega),postMem,fr5 _ (word_ne_of_toNat (by rw [kNat,show (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 from hdrP 64 (by omega)]; omega))
        (Or.inl (by rw [kNat]; omega)),ct4 _ (by rw [c8Nat]; omega) (by omega),
      R3Below _ (by rw [word_add_toNat order _ (by omega)]; omega),← slot8 order k (by omega)]
    exact hx


#print axioms htabCopy_returned_aligned

theorem htabCopy_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (table : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htab_copy") [.val (.word table)] =
      some (sourceFunctionBody Guest.guestFn_htab_copy,HolFiniteMapExact.empty.update (ofString "t",.val (.word table)),.one) :=
  pan_single_word_lookup state.code.lookup (ofString "htab_copy") (ofString "t") (sourceFunctionBody Guest.guestFn_htab_copy)
    table (by rw [code]; exact originalRuntimeCode_hashCopy_lookup)

/-- The copy contract from an actual call entry on a word argument. -/
theorem htabCopy_entry_returned {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (above : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (cap8 : 8 ≤ capacity.toNat) (budget : htabCopyCost capacity stride + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))))
      (sourceFunctionBody Guest.guestFn_htab_copy) = (some (.returned v),post)) :
    ∃ keys' used' values' order' orderPos' : BitVec 64, v = .val (.word pointer) ∧
      HtabAligned keyLength pointer keys' stride capacity used' values' order' orderPos' count bits post ∧
      OrderInv post capacity count used' order' orderPos' ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w :=
  htabCopy_returned_aligned (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))))
    post v keyLength table keys stride capacity used values order orderPos count pointer bits (inv.transfer rfl rfl rfl rfl)
    (tables.transfer rfl rfl rfl) (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned pointerInside above (fun a h1 h2 h3 => by exact arena a h1 h2 h3) cap8
    (by change _ ≤ state.clock - 1; omega) run

/-- The original table copy keeps every non-heap global and moves an aligned
in-arena heap word only upward inside the arena, on continuing outcomes. -/
theorem htabCopy_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_copy) := by
  have pre := heapRel_preorder
  rw [source_htabCopy_body]
  repeat (first
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returnedRel
    | apply normalRel_dec pre
    | apply normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memcpy_lookup memcpy_returnedRel)
    | apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
    | exact heapRel_leaf (fun _ => rfl))

#print axioms htabCopy_installed
#print axioms htabCopy_entry_returned
#print axioms htabCopy_normalRel
end InitECandidate.Runtime

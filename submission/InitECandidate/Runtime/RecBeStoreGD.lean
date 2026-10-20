import InitECandidate.Runtime.RecSecpLeafGD
import InitECandidate.Runtime.OriginalBswap64Code
import InitECandidate.Runtime.OriginalStoreBE32Code
import InitECandidate.Runtime.OriginalStoreBE64Code
import InitECandidate.Runtime.VmFn_u256_to_be32
/-!
Window specs of the big-endian writers: `st_be32` / `st_be64` / `u256_to_be32` write only `[P, P + 4)`,
`[P, P + 8)`, `[O, O + 32)`; `bswap64` keeps memory and globals and returns a word.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def bswBody : ProgHOL 64 :=
  (.seq (.assign .local (ofString "x") (.op .or [(.shift .lsl (.op .and [(.var .local (ofString "x")),(.const 71777214294589695)]) (.const 8)),(.op .and [(.shift .lsr (.var .local (ofString "x")) (.const 8)),(.const 71777214294589695)])])) (.seq (.assign .local (ofString "x") (.op .or [(.shift .lsl (.op .and [(.var .local (ofString "x")),(.const 281470681808895)]) (.const 16)),(.op .and [(.shift .lsr (.var .local (ofString "x")) (.const 16)),(.const 281470681808895)])])) (.return (.op .or [(.shift .lsl (.var .local (ofString "x")) (.const 32)),(.shift .lsr (.var .local (ofString "x")) (.const 32))]))))

theorem bswBody_eq : sourceFunctionBody Guest.guestFn_bswap64 = bswBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_bswap64,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sb32Body : ProgHOL 64 :=
  (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24))) (.seq (.storeByte (.op .add [(.var .local (ofString "p")),(.const 1)]) (.shift .lsr (.var .local (ofString "v")) (.const 16))) (.seq (.storeByte (.op .add [(.var .local (ofString "p")),(.const 2)]) (.shift .lsr (.var .local (ofString "v")) (.const 8))) (.seq (.storeByte (.op .add [(.var .local (ofString "p")),(.const 3)]) (.var .local (ofString "v"))) (.return (.const 0))))))

theorem sb32Body_eq : sourceFunctionBody Guest.guestFn_st_be32 = sb32Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_st_be32,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sb64Body : ProgHOL 64 :=
  (.seq (.ite (.cmp .equal (.op .and [(.var .local (ofString "p")),(.const 7)]) (.const 0)) (.decCall (ofString "w") .one (ofString "bswap64") [(.var .local (ofString "v"))] (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) (.return (.const 0)))) .skip) (.seq (.call (some (none,none)) (ofString "st_be32") [(.var .local (ofString "p")),(.shift .lsr (.var .local (ofString "v")) (.const 32))]) (.seq (.call (some (none,none)) (ofString "st_be32") [(.op .add [(.var .local (ofString "p")),(.const 4)]),(.var .local (ofString "v"))]) (.return (.const 0)))))

theorem sb64Body_eq : sourceFunctionBody Guest.guestFn_st_be64 = sb64Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_st_be64,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def u2bBody : ProgHOL 64 :=
  (.seq (.ite (.cmp .equal (.op .and [(.var .local (ofString "out")),(.const 7)]) (.const 0)) (.decCall (ofString "w") .one (ofString "bswap64") [(.rfield 3 (.var .local (ofString "a")))] (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w"))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "bswap64") [(.rfield 2 (.var .local (ofString "a")))]) (.seq (.store (.op .add [(.var .local (ofString "out")),(.const 8)]) (.var .local (ofString "w"))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "bswap64") [(.rfield 1 (.var .local (ofString "a")))]) (.seq (.store (.op .add [(.var .local (ofString "out")),(.const 16)]) (.var .local (ofString "w"))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "bswap64") [(.rfield 0 (.var .local (ofString "a")))]) (.seq (.store (.op .add [(.var .local (ofString "out")),(.const 24)]) (.var .local (ofString "w"))) (.return (.const 0)))))))))) .skip) (.seq (.call (some (none,none)) (ofString "st_be64") [(.var .local (ofString "out")),(.rfield 3 (.var .local (ofString "a")))]) (.seq (.call (some (none,none)) (ofString "st_be64") [(.op .add [(.var .local (ofString "out")),(.const 8)]),(.rfield 2 (.var .local (ofString "a")))]) (.seq (.call (some (none,none)) (ofString "st_be64") [(.op .add [(.var .local (ofString "out")),(.const 16)]),(.rfield 1 (.var .local (ofString "a")))]) (.seq (.call (some (none,none)) (ofString "st_be64") [(.op .add [(.var .local (ofString "out")),(.const 24)]),(.rfield 0 (.var .local (ofString "a")))]) (.return (.const 0)))))))

theorem u2bBody_eq : sourceFunctionBody Guest.guestFn_u256_to_be32 = u2bBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_u256_to_be32,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

theorem mwin_shift {Dd w : BitVec 64} {N : Nat} (out : ¬ MWin Dd N w) (c n : Nat) (h : c + n ≤ N) :
    ¬ MWin (Dd + BitVec.ofNat 64 c) n w := fun ⟨j,hj,e⟩ =>
  out ⟨c + j,by omega,by rw [← ofNat_add_add]; exact e⟩

section be
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

/-- `bswap64` keeps memory and globals and returns a word. -/
theorem bswap_wn (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False) (fun _ M G => M = M0 ∧ G = G0) (fun _ _ _ => True)
      (fun r M G => (∃ y : BitVec 64, r = .val (.word y)) ∧ M = M0 ∧ G = G0)
      (sourceFunctionBody Guest.guestFn_bswap64) := by
  rw [bswBody_eq]; unfold bswBody
  refine aqgd_seq (Q := fun _ M G => M = M0 ∧ G = G0) (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ => pre)) ?_
  refine aqgd_seq (Q := fun _ M G => M = M0 ∧ G = G0) (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ => pre)) ?_
  exact aqgd_return _ (fun s v _ _ _ pre _ ev => ⟨isWord_op s _ _ v ev,pre⟩)

/-- `st_be32(p, v)` writes only `[P, P + 4)`. -/
theorem stBe32_wn (P : BitVec 64) (out : ¬ MWin P 4 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_st_be32) := by
  rw [sb32Body_eq]; unfold sb32Body
  have st : ∀ (j : Nat) (d v : ExpHOL 64), j < 4 → (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.locals.lookup (ofString "p") = some (.val (.word P)) → EV s d = some (.val (.word (P + BitVec.ofNat 64 j)))) →
      AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
        (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P))) (fun _ _ _ => True) (.storeByte d v) :=
    fun j d v hj hd => aqgd_storeByte _ _ (fun s _ _ pre _ => ⟨_,hd s pre,fun e => out ⟨j,hj,Or.inr e⟩,
      fun _ _ => pre⟩)
  refine aqgd_seq (st 0 _ _ (by decide) (fun s hp => by simp [EV,evalHOLExact,hp])) ?_
  refine aqgd_seq (st 1 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (st 2 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (st 3 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms stBe32_wn

/-- Callee entry `p` of `f(e1, e2)` where `e1` evaluates to `P`. -/
theorem entry_p {f : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(ofString "p",.one),(ofString "v",.one)],bd,rs0))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (P : BitVec 64)
    (h1 : EV s e1 = some (.val (.word P))) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA}
    {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup (ofString "p") = some (.val (.word P)) := by
  obtain ⟨v1,vs,rfl,e1',r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h1] at e1'; simp only [Option.some.injEq] at e1'; subst e1'
  have e := callee_eq inst lookup
  rw [e]; simp (config := {decide := true})

/-- `st_be64(p, v)` writes only `[P, P + 8)`. -/
theorem stBe64_wn (P : BitVec 64) (out : ¬ MWin P 8 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_st_be64) := by
  rw [sb64Body_eq]; unfold sb64Body
  let LP := fun L : GA => L.lookup (ofString "p") = some (.val (.word P))
  refine aqgd_seq (Q := fun L _ _ => LP L) (aqgd_iteT _ ?_ aqgd_skip) ?_
  · refine aqgd_decCallSpecF
      (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
      (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (r : ValueHOL 64) (M' : Mem) (G' : GA) =>
        (∃ y : BitVec 64, r = .val (.word y)) ∧ M' = M0' ∧ G' = G0')
      (Pc := fun L _ _ => LP L ∧ ∃ y : BitVec 64, L.lookup (ofString "w") = some (.val (.word y)))
      (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_bswap64_lookup
      (fun _ M0' G0' _ => bswap_wn M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_
      (fun _ _ _ _ _ _ _ h => h.elim)
    · intro L M G v M' G' hp ⟨⟨y,hy⟩,_⟩ _
      subst hy
      exact ⟨by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact hp,y,lookup_update_eq' _ _ _⟩
    refine aqgd_seq (aqgd_store (Q := fun _ _ _ => True) _ _ ?_ ?_) (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))
    · intro F s H _ _ ⟨hp,_⟩ _
      have hp : s.locals.lookup (ofString "p") = some (.val (.word P)) := hp
      exact ⟨P,by simp [EV,evalHOLExact,hp],fun e => out ⟨0,by decide,Or.inl (by simpa using e)⟩,fun _ _ => trivial⟩
    · intro F s x H _ _ ⟨_,y,hy⟩ _ ev
      simp [EV,evalHOLExact,hy] at ev; exact ⟨y,ev.symm⟩
  refine aqgd_seq (aqgd_callWin (LP := LP) _ _ _ _ _ originalRuntimeCode_storeBE32_lookup (by simp)
    (fun _ L => L.lookup (ofString "p") = some (.val (.word P)))
    (fun _ _ M0 G0 => aqgd_conseq (stBe32_wn P (mwin_mono (by decide) out)) (fun _ _ _ h => h.1)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (fun s values callee rs _ hp args lookup => entry_p originalRuntimeCode_storeBE32_lookup s _ _ P
      (by simp [EV,evalHOLExact,(show s.locals.lookup (ofString "p") = some (.val (.word P)) from hp)]) args lookup)) ?_
  refine aqgd_seq (aqgd_callWin (LP := LP) _ _ _ _ _ originalRuntimeCode_storeBE32_lookup (by simp)
    (fun _ L => L.lookup (ofString "p") = some (.val (.word (P + 4#64))))
    (fun _ _ M0 G0 => aqgd_conseq (stBe32_wn (P + 4#64) (mwin_shift out 4 4 (by decide))) (fun _ _ _ h => h.1)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (fun s values callee rs _ hp args lookup => entry_p originalRuntimeCode_storeBE32_lookup s _ _ _
      (by simp [EV,evalHOLExact,evalListHOLExact,(show s.locals.lookup (ofString "p") = some (.val (.word P)) from hp),
        wordOpHOL,wordOp,valueIsWord,valueWord]) args lookup)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms stBe64_wn

/-- `u256_to_be32(a, out)` writes only `[O, O + 32)`. -/
theorem u2b_wn (O : BitVec 64) (out : ¬ MWin O 32 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "out") = some (.val (.word O)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_u256_to_be32) := by
  rw [u2bBody_eq]; unfold u2bBody
  let LP := fun L : GA => L.lookup (ofString "out") = some (.val (.word O))
  let LW := fun L : GA => LP L ∧ ∃ y : BitVec 64, L.lookup (ofString "w") = some (.val (.word y))
  have stw : ∀ (k : Nat) (d : ExpHOL 64), k < 32 → (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      LP s.locals → EV s d = some (.val (.word (O + BitVec.ofNat 64 k)))) →
      AQGD D B A w (fun _ => False) (fun L _ _ => LW L) (fun L _ _ => LW L) (fun _ _ _ => True)
        (.store d (.var .local (ofString "w"))) := fun k d hk hd =>
    aqgd_store _ _ (fun s H _ hG pre _ => ⟨_,hd s (by unfold GIs at hG; subst hG; exact pre.1),
      fun e => out ⟨k,hk,Or.inl e⟩,fun _ _ => by unfold GIs at hG; subst hG; exact pre⟩)
      (fun s x H _ hG ⟨_,y,hy⟩ _ ev => by simp [EV,evalHOLExact,hy] at ev; exact ⟨y,ev.symm⟩)
  have caw : ∀ (e : ExpHOL 64),
      AQGD D B A w (fun _ => False) (fun L _ _ => LW L) (fun L _ _ => LW L) (fun _ _ _ => True)
        (.call (some (some (.local,ofString "w"),none)) (ofString "bswap64") [e]) := fun e =>
    aqgd_callAssignF (Vn' := fun _ => False)
      (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
      (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (r : ValueHOL 64) (M' : Mem) (G' : GA) =>
        (∃ y : BitVec 64, r = .val (.word y)) ∧ M' = M0' ∧ G' = G0')
      _ _ _ _ _ _ originalRuntimeCode_bswap64_lookup (by simp) (fun h => h)
      (fun _ M0' G0' _ => bswap_wn M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
      (fun L M G v M' G' ⟨hp,_⟩ ⟨⟨y,hy⟩,_⟩ => by
        subst hy
        exact ⟨by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact hp,y,lookup_update_eq' _ _ _⟩)
  have ho : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      s.locals.lookup (ofString "out") = some (.val (.word O)) := fun _ h => h
  refine aqgd_seq (Q := fun L _ _ => LP L) (aqgd_iteT _ ?_ aqgd_skip) ?_
  · refine aqgd_decCallSpecF
      (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
      (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (r : ValueHOL 64) (M' : Mem) (G' : GA) =>
        (∃ y : BitVec 64, r = .val (.word y)) ∧ M' = M0' ∧ G' = G0')
      (Pc := fun L _ _ => LW L) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_bswap64_lookup
      (fun _ M0' G0' _ => bswap_wn M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_
      (fun _ _ _ _ _ _ _ h => h.elim)
    · intro L M G v M' G' hp ⟨⟨y,hy⟩,_⟩ _
      subst hy
      exact ⟨by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact hp,y,lookup_update_eq' _ _ _⟩
    refine aqgd_seq (stw 0 _ (by decide) (fun s hp => by simp [EV,evalHOLExact,ho s hp])) ?_
    refine aqgd_seq (caw _) (aqgd_seq (stw 8 _ (by decide) (fun s hp => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_)
    refine aqgd_seq (caw _) (aqgd_seq (stw 16 _ (by decide) (fun s hp => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_)
    refine aqgd_seq (caw _) (aqgd_seq (stw 24 _ (by decide) (fun s hp => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_)
    exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)
  have cb : ∀ (k : Nat) (e1 e2 : ExpHOL 64), k + 8 ≤ 32 → (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      LP s.locals → EV s e1 = some (.val (.word (O + BitVec.ofNat 64 k)))) →
      AQGD D B A w (fun _ => False) (fun L _ _ => LP L) (fun L _ _ => LP L) (fun _ _ _ => True)
        (.call (some (none,none)) (ofString "st_be64") [e1,e2]) := fun k e1 e2 hk hd =>
    aqgd_callWin (LP := LP) _ _ _ _ _ originalRuntimeCode_storeBE64_lookup (by simp)
      (fun _ L => L.lookup (ofString "p") = some (.val (.word (O + BitVec.ofNat 64 k))))
      (fun _ _ M0 G0 => aqgd_conseq (stBe64_wn _ (mwin_shift out k 8 hk)) (fun _ _ _ h => h.1)
        (fun _ _ _ h => h) (fun _ _ _ h => h))
      (fun s values callee rs _ hp args lookup => entry_p originalRuntimeCode_storeBE64_lookup s _ _ _ (hd s hp)
        args lookup)
  refine aqgd_seq (cb 0 _ _ (by decide) (fun s hp => by simp [EV,evalHOLExact,ho s hp])) ?_
  refine aqgd_seq (cb 8 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (cb 16 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (cb 24 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,ho s hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms u2b_wn
end be
end InitECandidate.Runtime

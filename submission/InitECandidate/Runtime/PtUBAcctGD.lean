import InitECandidate.Runtime.PtUBBodyGD
/-!
The account item of `update_builder_from_tx`: the post-state reload (`ubChgReload`) and the change decisions
(`ubChgRest`: balance, nonce, code) in the builder world.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ubChgReload : ProgHOL 64 :=
  ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "post")) (ExpHOL.const 1#64)) ((ProgHOL.assign VarKind.local (ofString "post_bal") (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "post"), ExpHOL.const 8#64]))).seq ((ProgHOL.assign VarKind.local (ofString "post_nonce") (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "post"), ExpHOL.const 0#64]))).seq (ProgHOL.assign VarKind.local (ofString "post_ch") (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "post"), ExpHOL.const 48#64]))))) ProgHOL.skip

def ubChgRest : ProgHOL 64 :=
  ProgHOL.decCall (ofString "eq") ShapeHOL.one (ofString "u256_eq") [ExpHOL.var VarKind.local (ofString "pre_bal"), ExpHOL.var VarKind.local (ofString "post_bal")] ((ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "eq")) (ExpHOL.const 0#64)) (ProgHOL.call (some (none, none)) (ofString "add_balance_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.var VarKind.local (ofString "idx"), ExpHOL.var VarKind.local (ofString "post_bal")]) (ProgHOL.call (some (none, none)) (ofString "bal_remove_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.const 16#64, ExpHOL.const 40#64, ExpHOL.var VarKind.local (ofString "idx")])).seq ((ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "pre_nonce")) (ExpHOL.var VarKind.local (ofString "post_nonce"))) (ProgHOL.call (some (none, none)) (ofString "add_nonce_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.var VarKind.local (ofString "idx"), ExpHOL.var VarKind.local (ofString "post_nonce")]) (ProgHOL.call (some (none, none)) (ofString "bal_remove_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.const 24#64, ExpHOL.const 16#64, ExpHOL.var VarKind.local (ofString "idx")])).seq ((ProgHOL.call (some (some (VarKind.local, ofString "eq"), none)) (ofString "memeq") [ExpHOL.var VarKind.local (ofString "pre_ch"), ExpHOL.var VarKind.local (ofString "post_ch"), ExpHOL.const 32#64]).seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "eq")) (ExpHOL.const 0#64)) (ProgHOL.decCall (ofString "code") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) (ofString "get_code") [ExpHOL.var VarKind.local (ofString "post_ch"), ExpHOL.var VarKind.local (ofString "addr")] (ProgHOL.call (some (none, none)) (ofString "add_code_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.var VarKind.local (ofString "idx"), ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "code")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "code"))])) (ProgHOL.call (some (none, none)) (ofString "bal_remove_change") [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.const 32#64, ExpHOL.const 24#64, ExpHOL.var VarKind.local (ofString "idx")])))))

theorem memLoads_ones_words (k : Nat) {a : BitVec 64} {dom : BitVec 64 → Prop} {inst : DecidablePred dom}
    {mem : BitVec 64 → HolWordLab 64} {ctx : StructContextHOLM} {vs : List (ValueHOL 64)}
    (h : @memLoadsHOLExact 64 _ (List.replicate k .one) a dom inst mem ctx = some vs) :
    vs.length = k ∧ ∀ v ∈ vs, ∃ y : BitVec 64, v = .val (.word y) := by
  induction k generalizing a vs with
  | zero => simp [memLoadsHOLExact] at h; subst h; simp
  | succ k ih =>
    rw [List.replicate_succ] at h
    simp only [memLoadsHOLExact] at h
    split at h
    · rename_i v vs' h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl,hw⟩ := ih h2
      refine ⟨by simp [hl],fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [memLoadHOLExact] at h1
        split at h1
        · simp only [Option.some.injEq] at h1; subst h1
          rcases (mem a) with ⟨y⟩
          exact ⟨y,rfl⟩
        · simp at h1
      · exact hw x hx
    · simp at h

theorem ev_load4_words {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (x : ValueHOL 64)
    (h : EV s (.load (.comb [.one,.one,.one,.one]) e) = some x) :
    ∃ a b c d : BitVec 64, x = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)] := by
  unfold EV at h
  simp only [evalHOLExact] at h
  split at h
  · split at h
    · simp only [memLoadHOLExact] at h
      split at h
      · rename_i vs hv
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hl,hw⟩ := memLoads_ones_words 4 hv
        match vs, hl, hw with
        | [v0,v1,v2,v3], _, hw =>
          obtain ⟨a,rfl⟩ := hw v0 (by simp)
          obtain ⟨b,rfl⟩ := hw v1 (by simp)
          obtain ⟨c,rfl⟩ := hw v2 (by simp)
          obtain ⟨d,rfl⟩ := hw v3 (by simp)
          exact ⟨a,b,c,d,rfl⟩
      · simp at h
    · simp at h
  · simp at h

#print axioms ev_load4_words

theorem lk_resVar {pairs : List (MlS × BitVec 64)} {L : GA} (h : LK pairs L) (x : MlS) (o : Option (ValueHOL 64))
    (hx : ∀ p ∈ pairs, p.1 ≠ x) : LK pairs (L.resVarEq (x,o)) := fun p hp => by
  rw [resVar_lookup_ne _ _ _ _ (hx p hp)]; exact h p hp

/-- The post-state value locals of the account item: a four-word balance and word nonce and code-hash pointer. -/
def PVL (L : GA) : Prop :=
  (∃ a b c d : BitVec 64, L.lookup (ofString "post_bal") =
    some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)])) ∧
  (∃ y : BitVec 64, L.lookup (ofString "post_nonce") = some (.val (.word y))) ∧
  (∃ y : BitVec 64, L.lookup (ofString "post_ch") = some (.val (.word y)))

section rl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}

theorem ubChgReload_aqgd (pairs : List (MlS × BitVec 64))
    (hpn : ∀ p ∈ pairs, p.1 ≠ ofString "post_bal" ∧ p.1 ≠ ofString "post_nonce" ∧ p.1 ≠ ofString "post_ch")
    (W : Mem → GA → Prop) :
    AQGD D B A w (fun _ => False) (fun L M G => (LK pairs L ∧ PVL L) ∧ W M G)
      (fun L M G => (LK pairs L ∧ PVL L) ∧ W M G) RR ubChgReload := by
  unfold ubChgReload
  refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  refine aqgd_seq (Q := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G)
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨lk,pv⟩,hw⟩,_⟩ _ ev => ?_)) ?_
  · obtain ⟨a,b,c,d,rfl⟩ := ev_load4_words s _ v ev
    exact ⟨⟨lk_update lk _ _ (fun p hp => (hpn p hp).1),⟨a,b,c,d,lookup_update_eq' _ _ _⟩,
      let ⟨y,hy⟩ := pv.2.1; ⟨y,by rw [lookup_update_ne' _ _ (by decide)]; exact hy⟩,
      let ⟨y,hy⟩ := pv.2.2; ⟨y,by rw [lookup_update_ne' _ _ (by decide)]; exact hy⟩⟩,hw⟩
  refine aqgd_seq (Q := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G)
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨lk,pv⟩,hw⟩ _ ev => ?_)) ?_
  · obtain ⟨y,rfl⟩ := ev_load1_word s _ v ev
    exact ⟨⟨lk_update lk _ _ (fun p hp => (hpn p hp).2.1),
      let ⟨a,b,c,d,h⟩ := pv.1; ⟨a,b,c,d,by rw [lookup_update_ne' _ _ (by decide)]; exact h⟩,
      ⟨y,lookup_update_eq' _ _ _⟩,
      let ⟨y,hy⟩ := pv.2.2; ⟨y,by rw [lookup_update_ne' _ _ (by decide)]; exact hy⟩⟩,hw⟩
  refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨lk,pv⟩,hw⟩ _ ev => ?_)
  obtain ⟨y,rfl⟩ := ev_load1_word s _ v ev
  exact ⟨⟨lk_update lk _ _ (fun p hp => (hpn p hp).2.2),
    let ⟨a,b,c,d,h⟩ := pv.1; ⟨a,b,c,d,by rw [lookup_update_ne' _ _ (by decide)]; exact h⟩,
    let ⟨y,hy⟩ := pv.2.1; ⟨y,by rw [lookup_update_ne' _ _ (by decide)]; exact hy⟩,
    ⟨y,lookup_update_eq' _ _ _⟩⟩,hw⟩

#print axioms ubChgReload_aqgd
end rl

end InitECandidate.Runtime

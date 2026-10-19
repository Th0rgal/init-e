import InitECandidate.Runtime.DivmnuWindowGD
import InitECandidate.Runtime.VmFn_u256_to_digits
import InitECandidate.Runtime.VmFn_digits_to_u256
import InitECandidate.Runtime.ProcessTxWritersGD
/-!
Window frame of the actual `digits_divmod`: a tail-call rule for memory-frame callees, callee-binding lemmas,
fixed-locals predicates, and `digitsDivmod_window` (the divisor digit count is at least one because the divisor is
nonzero, so `divmnu` runs within its digit bounds).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section tc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A tail call to a memory-and-globals-keeping function: memory and globals unchanged in every outcome; a return
satisfies any return condition that holds at entry. -/
theorem aqgd_tailCall_mf {P Q : GA → Mem → GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (hr : ∀ L M G, P L M G → ∀ v, RR v M G) :
    AQGD D B A w Vn P Q RR (.call none function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · obtain ⟨m,g⟩ := mf (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at m g
          change bodyPost.memory = state.memory at m
          change bodyPost.globals = state.globals at g
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact ⟨by simp [m],fun _ => by simp [g]; exact aw,(fun e => by cases e),
                fun v' e => ⟨H,by unfold GIs; simp [g]; exact hH,by simp [m]; exact hr _ _ _ pre v'⟩,by simp,by simp⟩
            | exact ⟨by simp [m,emptyLocalsHOLFinite],fun _ => by simp [g,emptyLocalsHOLFinite]; exact aw,(fun e => by cases e),
                fun v' e => ⟨H,by unfold GIs; simp [g,emptyLocalsHOLFinite]; exact hH,
                  by simp [m,emptyLocalsHOLFinite]; exact hr _ _ _ pre v'⟩,by simp,by simp⟩
            | exact aqgd_of_nc (by simp [m]) (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqgd_tailCall_mf
end tc

/-- Callee locals of an installed function: each parameter bound to its argument value. -/
theorem callee_eq {f : MlS} {ps : List (MlS × ShapeHOL)} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some (ps,bd,rs0)) {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup = List.foldl (fun (map : MlS → Option (ValueHOL 64)) (entry : MlS × ValueHOL 64) =>
      fun current => if current = entry.1 then some entry.2 else map current) (fun _ => none)
      ((ps.map Prod.fst).zip values) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs1 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    rw [hl]
    unfold Flapjack.lookupCodeHOLExact at found
    rw [inst] at found
    dsimp only at found
    split at found
    · simp only [Option.some.injEq,Prod.mk.injEq] at found
      exact found.2.1.symm
    · cases found

#print axioms callee_eq

/-- Fixed one-binding-per-name locals. -/
def FixL (l : List (MlS × ValueHOL 64)) (L : GA) : Prop := ∀ p ∈ l, L.lookup p.1 = some p.2

theorem fixL_get {l : List (MlS × ValueHOL 64)} {L : GA} (h : FixL l L) (x : MlS) (v : ValueHOL 64)
    (hm : (x,v) ∈ l) : L.lookup x = some v := h (x,v) hm

theorem fixL_upd {l : List (MlS × ValueHOL 64)} {L : GA} (h : FixL l L) (name : MlS) (v : ValueHOL 64)
    (hn : name ∉ l.map Prod.fst) : FixL l (L.update (name,v)) := fun p hp => by
  rw [lookup_update_ne' _ _ (fun e => hn (List.mem_map.mpr ⟨p,hp,e⟩))]; exact h p hp

theorem fixL_res {l : List (MlS × ValueHOL 64)} {L : GA} (h : FixL l L) (name : MlS) (o : Option (ValueHOL 64))
    (hn : name ∉ l.map Prod.fst) : FixL l (L.resVarEq (name,o)) := fun p hp => by
  rw [resVarEq_lookup_ne' _ _ _ _ (fun e => hn (List.mem_map.mpr ⟨p,hp,e⟩))]; exact h p hp

theorem dig_ne {d0 d1 d2 d3 : BitVec 64} (h : ¬ (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0)) :
    ∃ j, j < 8 ∧ dig d0 d1 d2 d3 j ≠ 0 := by
  by_contra hc
  simp only [not_exists,not_and,not_not] at hc
  exact h ⟨half_zero d0 (hc 0 (by omega)) (hc 1 (by omega)),half_zero d1 (hc 2 (by omega)) (hc 3 (by omega)),
    half_zero d2 (hc 4 (by omega)) (hc 5 (by omega)),half_zero d3 (hc 6 (by omega)) (hc 7 (by omega))⟩

theorem ofNat_mul8 (P : BitVec 64) (j : Nat) (hj : j < 8) :
    P + BitVec.ofNat 64 j * 8 = P + BitVec.ofNat 64 (8 * j) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul,BitVec.toNat_ofNat]
  omega

#print axioms dig_ne

def ddBody : ProgHOL 64 :=
  ProgHOL.dec (ofString "q") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 216#64]) (ProgHOL.dec (ofString "r") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 352#64]) (ProgHOL.dec (ofString "v") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 560#64]) (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "u256_to_digits") [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.var VarKind.local (ofString "d")]) (ProgHOL.decCall (ofString "n") ShapeHOL.one (ofString "digits_len") [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.const 8#64] (ProgHOL.decCall (ofString "mm") ShapeHOL.one (ofString "digits_len") [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.var VarKind.local (ofString "m")] (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.const 16#64)) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "mm")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.call none (ofString "digits_to_u256") [ExpHOL.var VarKind.local (ofString "u")]) ProgHOL.skip) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.const 8#64)) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))) (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "divmnu") [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "r"), ExpHOL.var VarKind.local (ofString "u"), ExpHOL.var VarKind.local (ofString "mm"), ExpHOL.var VarKind.local (ofString "v"), ExpHOL.var VarKind.local (ofString "n")]) (ProgHOL.call none (ofString "digits_to_u256") [ExpHOL.var VarKind.local (ofString "r")]))))))))))))

theorem ddBody_eq : sourceFunctionBody Guest.guestFn_digits_divmod = ddBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_digits_divmod,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
theorem fixL_cons {l : List (MlS × ValueHOL 64)} {L : GA} (h : FixL l L) (name : MlS) (v : ValueHOL 64)
    (hn : name ∉ l.map Prod.fst) : FixL ((name,v) :: l) (L.update (name,v)) := by
  intro p hp
  rcases List.mem_cons.mp hp with e | hp
  · subst e; exact lookup_update_eq' _ _ _
  · exact fixL_upd h name v hn p hp

/-- The eight digits of `d` at `U + 560`. -/
def DigOK (U d0 d1 d2 d3 : BitVec 64) (M : Mem) : Prop :=
  ∀ k, k < 8 → M (U + 560#64 + BitVec.ofNat 64 (8 * k)) = .word (dig d0 d1 d2 d3 k)

/-- `n` holds a digit count in `[1, 8]`. -/
def NB (L : GA) : Prop :=
  ∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)) ∧ 1 ≤ N.toNat ∧ N.toNat ≤ 8

/-- `mm` holds a digit count in `[0, 8]`. -/
def MMB (L : GA) : Prop :=
  ∃ MM : BitVec 64, L.lookup (ofString "mm") = some (.val (.word MM)) ∧ MM.toNat ≤ 8

/-- The word held in local `x` (zero if none). -/
def wordOf (L : GA) (x : MlS) : BitVec 64 :=
  match L.lookup x with | some (.val (.word y)) => y | _ => 0

theorem wordOf_eq {L : GA} {x : MlS} {y : BitVec 64} (h : L.lookup x = some (.val (.word y))) : wordOf L x = y := by
  unfold wordOf; rw [h]

/-- `n ≤ mm` for the digit counts in `n`, `mm`. -/
def GE (L : GA) : Prop :=
  ∀ N MM : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)) →
    L.lookup (ofString "mm") = some (.val (.word MM)) → N.toNat ≤ MM.toNat

/-- `i` holds a word. -/
def IW (L : GA) : Prop := ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I))

/-- Fixed locals of `digits_divmod(u, m, d)` after its three workspace pointers. -/
def ddL (U Uu Mw d0 d1 d2 d3 : BitVec 64) : List (MlS × ValueHOL 64) :=
  [(ofString "v",.val (.word (U + 560#64))),(ofString "r",.val (.word (U + 352#64))),
    (ofString "q",.val (.word (U + 216#64))),(ofString "u",.val (.word Uu)),(ofString "m",.val (.word Mw)),
    (ofString "d",.rStruct [.val (.word d0),.val (.word d1),.val (.word d2),.val (.word d3)])]

section dd
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}
  {U Uu Mw d0 d1 d2 d3 : BitVec 64}

theorem digitsDivmod_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (hM8 : Mw.toNat ≤ 8) (hd : ¬ (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0)) :
    AQGD D B A w (fun x => x ≠ ofString "d")
      (fun L _ _ => FixL [(ofString "u",.val (.word Uu)),(ofString "m",.val (.word Mw)),
        (ofString "d",.rStruct [.val (.word d0),.val (.word d1),.val (.word d2),.val (.word d3)])] L)
      (fun _ _ _ => False) (fun _ _ _ => True) ddBody := by
  unfold ddBody
  have gl : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) v, A s.globals →
      EV s (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const k]) = some v →
      v = .val (.word (U + k)) := by
    intro F s k v aw ev
    have hg := hA _ aw
    unfold WsG at hg
    simp [EV,evalHOLExact,evalListHOLExact,hg,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    exact ev.symm
  refine r_dec (LQ' := fun _ => False) _ _ _ (fun _ => rfl) (fun s v aw lp ev => by
    rw [gl s _ v aw ev]; exact fixL_cons lp _ _ (by simp only [List.map_cons,List.map_nil]; decide)) ?_ (fun _ _ _ h => h)
  refine r_dec (LQ' := fun _ => False) _ _ _ (fun _ => rfl) (fun s v aw lp ev => by
    rw [gl s _ v aw ev]; exact fixL_cons lp _ _ (by simp only [List.map_cons,List.map_nil]; decide)) ?_ (fun _ _ _ h => h)
  refine r_dec (LQ' := fun _ => False) _ _ _ (fun _ => rfl) (fun s v aw lp ev => by
    rw [gl s _ v aw ev]; exact fixL_cons lp _ _ (by simp only [List.map_cons,List.map_nil]; decide)) ?_ (fun _ _ _ h => h)
  -- u256_to_digits(v, d)
  have hwk : ∀ k, k < 8 → w ≠ U + 560#64 + BitVec.ofNat 64 (8 * k) := by
    intro k hk e; apply hw; subst e; unfold WS; simp [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  refine aqgd_seq (Q := fun L M _ => FixL (ddL U Uu Mw d0 d1 d2 d3) L ∧ DigOK U d0 d1 d2 d3 M)
    (aqgd_callSpecS (Vn' := fun _ => False)
      (Pe := fun (_ : GA) (M0' : Mem) (_ : GA) (L : GA) (M : Mem) (_ : GA) => LPA (U + 560#64) d0 d1 d2 d3 L ∧ M = M0')
      (RRe := fun (_ : GA) (M0' : Mem) (_ : GA) (_ : ValueHOL 64) (M' : Mem) (_ : GA) =>
        U2D (U + 560#64) d0 d1 d2 d3 M0' 8 M')
      _ _ _ _ _ vmLookup_u256_to_digits (fun _ _ _ _ _ h => h.elim)
      (fun _ M0' _ _ => by
        rw [u2dBody_eq]
        exact aqgd_conseq (u2d_spec (M0 := M0') hwk) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
      ?_ ?_) ?_
  · intro F s values callee rs _ _ _ lp _ args lookup
    have hv := fixL_get lp (ofString "v") (.val (.word (U + 560#64))) (by simp [ddL])
    have hd' := fixL_get lp (ofString "d")
      (.rStruct [.val (.word d0),.val (.word d1),.val (.word d2),.val (.word d3)]) (by simp [ddL])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hv,hd'] at args
    subst args
    refine ⟨?_,rfl⟩
    have e := callee_eq vmLookup_u256_to_digits lookup
    unfold LPA; rw [e]; simp; decide
  · intro L M _ _ M' _ lp post
    exact ⟨lp,fun k hk => post.2 k hk⟩
  -- n = digits_len(v, 8): at least one digit of the nonzero divisor is nonzero
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "p") = some (.val (.word (U + 560#64))) ∧ L.lookup (ofString "n") = some (.val (.word 8#64)) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      M' = M0' ∧ G' = G0' ∧ DLRetW (U + 560#64) 8#64 M0' v)
    (Pc := fun L _ _ => FixL (ddL U Uu Mw d0 d1 d2 d3) L ∧ NB L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_digitsLen_lookup (by simp)
    (fun _ M0' G0' _ => by
      rw [dlBody_eq]
      exact aqgd_conseq (digitsLen_spec _ _ M0' G0') (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨lp,_⟩ _ args lookup
    have hv := fixL_get lp (ofString "v") (.val (.word (U + 560#64))) (by simp [ddL])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hv] at args
    subst args
    have e := callee_eq originalRuntimeCode_digitsLen_lookup lookup
    refine ⟨?_,?_,rfl,rfl⟩ <;> (rw [e]; simp) <;> (intro h; exact absurd h (by decide))
  · intro L M G v M' G' ⟨lp,dg⟩ ⟨_,_,N,hvN,hle,hnz⟩ _
    subst hvN
    obtain ⟨j,hj,hne⟩ := dig_ne hd
    have one : 1 ≤ N.toNat := hnz ⟨BitVec.ofNat 64 j,by simp [BitVec.toNat_ofNat]; omega,by
      rw [ofNat_mul8 _ _ hj,dg j hj]; simpa using hne⟩
    exact ⟨fixL_upd lp _ _ (by simp only [ddL,List.map_cons,List.map_nil]; decide),N,lookup_update_eq' _ _ _,one,
      by simpa using hle⟩
  -- mm = digits_len(u, m)
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "p") = some (.val (.word Uu)) ∧ L.lookup (ofString "n") = some (.val (.word Mw)) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      M' = M0' ∧ G' = G0' ∧ DLRetW Uu Mw M0' v)
    (Pc := fun L _ _ => FixL (ddL U Uu Mw d0 d1 d2 d3) L ∧ NB L ∧ MMB L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_digitsLen_lookup (by simp)
    (fun _ M0' G0' _ => by
      rw [dlBody_eq]
      exact aqgd_conseq (digitsLen_spec _ _ M0' G0') (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨lp,_⟩ _ args lookup
    have hu := fixL_get lp (ofString "u") (.val (.word Uu)) (by simp [ddL])
    have hm := fixL_get lp (ofString "m") (.val (.word Mw)) (by simp [ddL])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hu,hm] at args
    subst args
    have e := callee_eq originalRuntimeCode_digitsLen_lookup lookup
    refine ⟨?_,?_,rfl,rfl⟩ <;> (rw [e]; simp) <;> (intro h; exact absurd h (by decide))
  · intro L M G v M' G' ⟨lp,⟨N,hn,h1,h8⟩⟩ ⟨_,_,MM,hvM,hle,_⟩ _
    subst hvM
    exact ⟨fixL_upd lp _ _ (by simp only [ddL,List.map_cons,List.map_nil]; decide),
      ⟨N,by rw [lookup_update_ne' _ _ (by decide)]; exact hn,h1,h8⟩,MM,lookup_update_eq' _ _ _,by omega⟩
  -- the locals-only remainder
  let S := fun L => FixL (ddL U Uu Mw d0 d1 d2 d3) L ∧ NB L ∧ MMB L
  have supd : ∀ L v, S L → S (L.update (ofString "i",v)) := by
    intro L v ⟨lp,⟨N,hn,h1,h8⟩,⟨MM,hm,h8'⟩⟩
    exact ⟨fixL_upd lp _ _ (by simp only [ddL,List.map_cons,List.map_nil]; decide),
      ⟨N,by rw [lookup_update_ne' _ _ (by decide)]; exact hn,h1,h8⟩,⟨MM,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,h8'⟩⟩
  have geupd : ∀ L v, GE L → GE (L.update (ofString "i",v)) := by
    intro L v ge N MM hn hm
    rw [lookup_update_ne' _ _ (by decide)] at hn hm; exact ge N MM hn hm
  refine r_dec (LB := fun L => S L ∧ IW L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl)
    (fun s v _ lp ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨supd _ _ lp,_,lookup_update_eq' _ _ _⟩) ?_ (fun _ _ _ h => h)
  -- clear the quotient digits q[0..16)
  refine aqgd_seq (r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < 16)
    _ ?_ (aqgd_seq (r_store U _ _ ?_ (fun s x _ _ _ ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩) hw)
      (r_assign _ _ ?_))) ?_
  · intro F s x _ ⟨_,I,hi⟩ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : I < 16#64
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨lp,_⟩,_⟩,I,hi,lt⟩
    have hq := fixL_get lp (ofString "q") (.val (.word (U + 216#64))) (by simp [ddL])
    refine ⟨U + 216#64 + I * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hq,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS; simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  · intro F s v _ ⟨⟨lp,_⟩,_⟩ ev
    obtain ⟨y,rfl⟩ := ev_op_word s _ _ _ ev
    exact ⟨supd _ _ lp,y,lookup_update_eq' _ _ _⟩
  -- early exit when the dividend is shorter than the divisor
  refine aqgd_seq (Q := fun L _ _ => (S L ∧ IW L) ∧ GE L)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => GE L) _ ?_
      (aqgd_tailCall_mf _ _ _ _ _ vmLookup_digits_to_u256
        (memoryFrame_of_good vmLookup_digits_to_u256 (by decide) (by decide)) (fun _ _ _ _ _ => trivial))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · intro F s x _ _ _ _ _ ev
    refine ⟨fun _ => trivial,fun z N MM hn hm => ?_⟩
    simp [EV,evalHOLExact,hn,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases h : MM < N
    · simp [h] at ev; subst z; exact absurd ev (by decide)
    · simp [BitVec.lt_def] at h; omega
  -- clear the remainder digits r[0..8)
  refine aqgd_seq (r_assign (LQ := fun L => (S L ∧ IW L) ∧ GE L) _ _ (fun s v _ ⟨⟨lp,_⟩,ge⟩ ev => by
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨supd _ _ lp,_,lookup_update_eq' _ _ _⟩,geupd _ _ ge⟩)) ?_
  refine aqgd_seq (r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < 8)
    _ ?_ (aqgd_seq (r_store U _ _ ?_ (fun s x _ _ _ ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩) hw)
      (r_assign _ _ ?_))) ?_
  · intro F s x _ ⟨⟨_,I,hi⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : I < 8#64
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨⟨lp,_⟩,_⟩,_⟩,I,hi,lt⟩
    have hr := fixL_get lp (ofString "r") (.val (.word (U + 352#64))) (by simp [ddL])
    refine ⟨U + 352#64 + I * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hr,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS; simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  · intro F s v _ ⟨⟨⟨lp,_⟩,ge⟩,_⟩ ev
    obtain ⟨y,rfl⟩ := ev_op_word s _ _ _ ev
    exact ⟨⟨supd _ _ lp,y,lookup_update_eq' _ _ _⟩,geupd _ _ ge⟩
  -- divmnu(q, r, u, mm, v, n), then the remainder
  refine aqgd_seq (Q := fun L _ _ => (S L ∧ IW L) ∧ GE L) (aqgd_callSpec (Vn' := fun x => x ≠ ofString "qr")
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      DVP U (wordOf L0 (ofString "mm")) (wordOf L0 (ofString "n")) L)
    (RRe := fun _ _ _ _ _ _ => True)
    _ _ _ _ _ originalRuntimeCode_divmnu_lookup (by simp) ?_ ?_ (fun _ _ _ _ _ _ pre _ => pre))
    (aqgd_tailCall_mf _ _ _ _ _ vmLookup_digits_to_u256
      (memoryFrame_of_good vmLookup_digits_to_u256 (by decide) (by decide)) (fun _ _ _ _ _ => trivial))
  · intro L0 M0 G0 ⟨⟨⟨_,⟨N,hn,h1,_⟩,⟨MM,hm,hm8⟩⟩,_⟩,ge⟩
    rw [wordOf_eq hm,wordOf_eq hn]
    exact aqgd_conseq (divmnu_window hA hU h1 (ge N MM hn hm) hm8 hw) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
  · intro F s values callee rs _ _ _ ⟨⟨⟨lp,⟨N,hn,_⟩,⟨MM,hm,_⟩⟩,_⟩,_⟩ _ args lookup
    have hq := fixL_get lp (ofString "q") (.val (.word (U + 216#64))) (by simp [ddL])
    have hr := fixL_get lp (ofString "r") (.val (.word (U + 352#64))) (by simp [ddL])
    have hu := fixL_get lp (ofString "u") (.val (.word Uu)) (by simp [ddL])
    have hv := fixL_get lp (ofString "v") (.val (.word (U + 560#64))) (by simp [ddL])
    rw [wordOf_eq hm,wordOf_eq hn]
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hq,hr,hu,hv,hm,hn] at args
    subst args
    have e := callee_eq originalRuntimeCode_divmnu_lookup lookup
    unfold DVP
    refine ⟨?_,?_,?_,?_⟩ <;> (rw [e]; simp) <;> (try decide) <;> rfl

#print axioms digitsDivmod_window

theorem digitsDivmod_window' {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w U Uu Mw d0 d1 d2 d3 : BitVec 64}
    (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (hM8 : Mw.toNat ≤ 8) (hd : ¬ (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0)) :
    AQGD D B A w (fun x => x ≠ ofString "d")
      (fun L _ _ => FixL [(ofString "u",.val (.word Uu)),(ofString "m",.val (.word Mw)),
        (ofString "d",.rStruct [.val (.word d0),.val (.word d1),.val (.word d2),.val (.word d3)])] L)
      (fun _ _ _ => False) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_digits_divmod) := by
  rw [ddBody_eq]; exact digitsDivmod_window hA hU hw hM8 hd

end dd
section dcs
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `aqgd_decCallSpec` with the callee-entry scalar locals supplied by the caller (any parameter shapes). -/
theorem aqgd_decCallSpecS {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hsl : ∀ values callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      SL Vn' callee)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQGD D B A w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQGD D B A w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := hsl values callee foundShape lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          esl H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                obtain ⟨H',hH',rr⟩ := r1 v rfl
                have pc := hret _ _ _ _ _ _ pre rr ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by obtain ⟨d1,d2,d3⟩ := dom; exact ⟨fun a ha => d1 a (meta'.2.1 ▸ ha),meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩)
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx H' (by exact hH') pc
                refine ⟨m2.trans m1,a2,fun e => ?_,r2,c2,b2⟩
                obtain ⟨sl2,H2,hH2,q2⟩ := n2 e
                exact ⟨sl_restore sl2 sl name,H2,hH2,hq _ _ _ _ _ _ pre q2⟩
              · exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- An existential precondition may be opened before building the triple. -/
theorem aqgd_exE {α : Type} {P : α → GA → Mem → GA → Prop} {Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : ∀ x, AQGD D B A w Vn (P x) Q RR p) : AQGD D B A w Vn (fun L M G => ∃ x, P x L M G) Q RR p :=
  fun F s code dom aw sl H hH ⟨x,px⟩ => h x F s code dom aw sl H hH px

#print axioms aqgd_decCallSpecS
end dcs

/-- Four-word value in local `x`. -/
def U4 (x : MlS) (L : GA) : Prop :=
  ∃ a0 a1 a2 a3 : BitVec 64, L.lookup x = some (.rStruct [.val (.word a0),.val (.word a1),.val (.word a2),.val (.word a3)])

/-- Callee entry of a function with two four-word parameters: both bound to four-word values, nothing else. -/
theorem callee_u4u4 {f p q : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.comb [.one,.one,.one,.one]),(q,.comb [.one,.one,.one,.one])],bd,rs0))
    (ne : p ≠ q) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    U4 p callee ∧ U4 q callee ∧ ∀ x, x ≠ p → x ≠ q → callee.lookup x = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs1 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [inst] at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0,v1], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,
          Bool.and_eq_true] at hall
        obtain ⟨s0,s1⟩ := hall
        obtain ⟨a0,a1,a2,a3,rfl⟩ := shape4' s0
        obtain ⟨b0,b1,b2,b3,rfl⟩ := shape4' s1
        subst hcl
        refine ⟨⟨a0,a1,a2,a3,by rw [hl]; simp [ne]⟩,⟨b0,b1,b2,b3,by rw [hl]; simp⟩,fun x h1 h2 => by rw [hl]; simp [h1,h2]⟩
    · cases found

#print axioms callee_u4u4

end InitECandidate.Runtime

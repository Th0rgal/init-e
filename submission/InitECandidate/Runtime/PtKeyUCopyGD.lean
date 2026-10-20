import InitECandidate.Runtime.PtKeyUCopyStepGD
import InitECandidate.Runtime.PtKeyULoopQGD
import InitECandidate.Runtime.MemcpyByte8Progress
import InitECandidate.Runtime.MemcpyByteSuffixBound
import InitECandidate.Runtime.MemeqByte8Bound
/-!
The byte-copy suffix of the source `memcpy` (eight-byte loop, single-byte loop, `return 0`) on ranges whose aligned
cells are addressable: it returns `0`, changes memory only in the destination's cells
`W = {align (dst + k) | k < n}`, keeps domain, endianness, globals and code, and spends at most `n / 8 + 8` clocks.
No alignment of either operand is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Destination cells written by `memcpy(dst, _, n)`. -/
def cpW (dst n : BitVec 64) (x : BitVec 64) : Prop := ∃ k : BitVec 64, k.toNat < n.toNat ∧ x = panByteAlignHOL (dst + k)

/-- `x + i + c` as a source address expression. -/
def cpA (x : MlS) (cs : List (BitVec 64)) : ExpHOL 64 :=
  .op .add ([.var .local x, .var .local (ofString "i")] ++ cs.map .const)

theorem bsStores_memcpyByte8 : bsStores memcpyByte8Body =
    [(cpA (ofString "dst") [], .loadByte (cpA (ofString "src") [])),
     (cpA (ofString "dst") [1], .loadByte (cpA (ofString "src") [1])),
     (cpA (ofString "dst") [2], .loadByte (cpA (ofString "src") [2])),
     (cpA (ofString "dst") [3], .loadByte (cpA (ofString "src") [3])),
     (cpA (ofString "dst") [4], .loadByte (cpA (ofString "src") [4])),
     (cpA (ofString "dst") [5], .loadByte (cpA (ofString "src") [5])),
     (cpA (ofString "dst") [6], .loadByte (cpA (ofString "src") [6])),
     (cpA (ofString "dst") [7], .loadByte (cpA (ofString "src") [7]))] := by
  rw [show memcpyByte8Body = (match memcpyByte8Loop with | .while _ body => body | _ => .skip) from rfl,
    memcpyByte8Loop_shape]
  rfl

theorem bsStores_memcpyByte1 : bsStores memcpyByte1Body =
    [(cpA (ofString "dst") [], .loadByte (cpA (ofString "src") []))] := by rfl

theorem bsNoDec_memcpyByte8 : bsNoDec memcpyByte8Body = true := by
  rw [show memcpyByte8Body = (match memcpyByte8Loop with | .while _ body => body | _ => .skip) from rfl,
    memcpyByte8Loop_shape]
  rfl

theorem bsNoDec_memcpyByte1 : bsNoDec memcpyByte1Body = true := by rfl

section cp
variable {F : Type}

theorem eval_cpA (state : PanSemStateFiniteExact 64 F) (x : MlS) (xv i : BitVec 64)
    (hx : state.locals.lookup x = some (.val (.word xv)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i))) (cs : List (BitVec 64)) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) (cpA x cs) =
      some (.val (.word (xv + (i + cs.foldr (· + ·) 0)))) := by
  have consts : ∀ ds : List (BitVec 64), @evalListHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (ds.map .const) =
        some (ds.map fun d => .val (.word d)) := by
    intro ds; induction ds with
    | nil => rfl
    | cons d rest ih => simp [evalListHOLExact, evalHOLExact, ih]
  unfold cpA
  rw [evalHOLExact]
  simp only [List.cons_append, List.nil_append]
  rw [evalListHOLExact, evalListHOLExact, consts cs]
  simp [evalHOLExact, hx, hi, valueIsWord, valueWord, wordOpHOL, wordOp, List.foldr_map]

/-- One store/value pair of the copy steps, read from an addressable source cell into an addressable destination
cell of the write set. -/
theorem cp_pair_ok (t : PanSemStateFiniteExact 64 F) (dst src n i : BitVec 64)
    (hd : t.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hs : t.locals.lookup (ofString "src") = some (.val (.word src)))
    (hi : t.locals.lookup (ofString "i") = some (.val (.word i)))
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      t.memaddrs (panByteAlignHOL (dst + x)) ∧ t.memaddrs (panByteAlignHOL (src + x)))
    (cs : List (BitVec 64)) (inR : (i + cs.foldr (· + ·) 0).toNat < n.toNat) :
    ∃ a w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address))
        (cpA (ofString "dst") cs) = some (.val (.word a)) ∧
      @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address))
        (.loadByte (cpA (ofString "src") cs)) = some (.val (.word w)) ∧
      t.memaddrs (panByteAlignHOL a) ∧ cpW dst n (panByteAlignHOL a) := by
  obtain ⟨cd, csrc⟩ := cells _ inR
  obtain ⟨c, hc⟩ : ∃ c : BitVec 64, t.memory (panByteAlignHOL (src + (i + cs.foldr (· + ·) 0))) = .word c := by
    cases t.memory (panByteAlignHOL (src + (i + cs.foldr (· + ·) 0))) with | word c => exact ⟨c, rfl⟩
  have hw : ∃ w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address))
      (.loadByte (cpA (ofString "src") cs)) = some (.val (.word w)) := by
    rw [evalHOLExact, eval_cpA t _ src i hs hi cs]
    simp [panMemLoadByteHOL, hc, csrc]
    exact csrc
  obtain ⟨w, hw⟩ := hw
  exact ⟨_, w, eval_cpA t _ dst i hd hi cs, hw, cd, ⟨_, inR, rfl⟩⟩

/-- Copy-loop invariant: operands bound, index in range, nonlocal fields fixed, memory changed only in `cpW`. -/
def CpInv (dst src n : BitVec 64) (M : BitVec 64 → HolWordLab 64) (D : BitVec 64 → Prop) (B : Bool)
    (G : HolFiniteMapExact MlS (ValueHOL 64)) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧ s.locals.lookup (ofString "src") = some (.val (.word src)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  (∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ n.toNat) ∧
  s.memaddrs = D ∧ s.be = B ∧ s.globals = G ∧ s.code = C ∧ (∀ x, ¬ cpW dst n x → s.memory x = M x)

variable {M : BitVec 64 → HolWordLab 64} {D : BitVec 64 → Prop} {B : Bool} {G : HolFiniteMapExact MlS (ValueHOL 64)}
  {C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}

/-- One copy step at index `i` with `k` bytes ahead: advance by `k`, memory changed only in `cpW`. -/
theorem cp_step {dst src n k : BitVec 64} {step : ProgHOL 64} (sup : ByteAdvanceStep (ofString "i") k step)
    (nd : bsNoDec step = true)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (dst + x)) ∧ D (panByteAlignHOL (src + x)))
    (s : PanSemStateFiniteExact 64 F) (i : BitVec 64) (hs : CpInv dst src n M D B G C s)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) (hkn : i.toNat + k.toNat ≤ n.toNat)
    (pairs : ∀ p ∈ bsStores step, ∃ cs : List (BitVec 64), (i + cs.foldr (· + ·) 0).toNat < n.toNat ∧
      p = (cpA (ofString "dst") cs, .loadByte (cpA (ofString "src") cs))) :
    evaluateHOLFiniteState s step = (none, (evaluateHOLFiniteState s step).2) ∧
      CpInv dst src n M D B G C (evaluateHOLFiniteState s step).2 ∧
      (evaluateHOLFiniteState s step).2.locals.lookup (ofString "i") = some (.val (.word (i + k))) ∧
      (evaluateHOLFiniteState s step).2.clock = s.clock := by
  obtain ⟨hd, hsr, hn, _, hD, hB, hG, hC, hM⟩ := hs
  obtain ⟨M', run, fr⟩ := evaluate_copyStep_ok sup (cpW dst n) s.locals D (fun t hl hdd p hp => by
      obtain ⟨cs, inR, rfl⟩ := pairs p hp
      exact cp_pair_ok t dst src n i (hl ▸ hd) (hl ▸ hsr) (hl ▸ hi) (fun x hx => by rw [hdd]; exact cells x hx) cs inR |>.imp
        fun a ⟨w, h1, h2, h3, h4⟩ => ⟨w, h1, h2, hdd ▸ h3, h4⟩)
    nd s rfl hD i hi
  have ia : ofString "i" ≠ ofString "dst" := by decide
  have is : ofString "i" ≠ ofString "src" := by decide
  have inn : ofString "i" ≠ ofString "n" := by decide
  rw [run]
  refine ⟨rfl, ⟨?_, ?_, ?_, ⟨i + k, ?_, ?_⟩, hD, hB, hG, hC, ?_⟩, ?_, rfl⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ia] using hd
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, is] using hsr
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, inn] using hn
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [BitVec.toNat_add_of_lt (by have := n.isLt; omega)]; omega
  · intro x hx
    change M' x = M x
    rw [fr x hx]; exact hM x hx
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem cp_dec {dst src n : BitVec 64} {s : PanSemStateFiniteExact 64 F} (h : CpInv dst src n M D B G C s) :
    CpInv dst src n M D B G C (decClockHOLFinite s) := h

theorem cp_inR (i n : BitVec 64) (k : Nat) (hk : i.toNat + k < n.toNat) (cs : List (BitVec 64))
    (hcs : cs.foldr (· + ·) 0 = BitVec.ofNat 64 k) : (i + cs.foldr (· + ·) 0).toNat < n.toNat := by
  rw [hcs, BitVec.toNat_add_of_lt] <;> simp <;> omega

theorem cp_loop8 {dst src n : BitVec 64} (small : n.toNat ≤ 33806089496)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (dst + x)) ∧ D (panByteAlignHOL (src + x)))
    (s : PanSemStateFiniteExact 64 F) (hs : CpInv dst src n M D B G C s)
    (budget : memeqByte8Rank n s ≤ s.clock) :
    ∃ post, evaluateHOLFiniteState s memcpyByte8Loop = (none, post) ∧
      s.clock ≤ post.clock + memeqByte8Rank n s ∧ post.clock ≤ s.clock ∧
      CpInv dst src n M D B G C post ∧ memeqByte8Rank n post = 0 := by
  let condition : ExpHOL 64 := memzeroBlockCondition 8
  have guard : ∀ current : PanSemStateFiniteExact 64 F, CpInv dst src n M D B G C current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if memeqByte8Rank n current = 0 then 0 else 1))) := by
    rintro current ⟨_, _, localN, ⟨i, localI, inside⟩, _⟩
    have rankEq : memeqByte8Rank n current = (n.toNat - i.toNat) / 8 := by simp [memeqByte8Rank, localI]
    have nextNat : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
      rfl
    by_cases done : memeqByte8Rank n current = 0
    · have outside : n < i + 8 := by
        apply BitVec.lt_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,memzeroBlockCondition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact outside
    · have below : i + 8 ≤ n := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,memzeroBlockCondition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact below
  have step : ∀ current : PanSemStateFiniteExact 64 F, CpInv dst src n M D B G C current → 0 < memeqByte8Rank n current →
      0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memcpyByte8Body = (none,post) ∧ CpInv dst src n M D B G C post ∧
            memeqByte8Rank n post < memeqByte8Rank n current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (fun _ _ => False) result post ∧
           evaluateHOLFiniteState current memcpyByte8Body = (some result,post))) := by
    intro current hc positive _
    obtain ⟨i, localI, inside⟩ := hc.2.2.2.1
    have rankEq : memeqByte8Rank n current = (n.toNat - i.toNat) / 8 := by simp [memeqByte8Rank, localI]
    have below : i.toNat + 8 ≤ n.toNat := by rw [rankEq] at positive; omega
    obtain ⟨run, inv, li, ck⟩ := cp_step memcpyByte8Body_supported bsNoDec_memcpyByte8 cells current i hc localI
      (by change i.toNat + 8 ≤ n.toNat; omega) (by
        rw [bsStores_memcpyByte8]
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨[], cp_inR i n 0 (by omega) [] rfl, rfl⟩
        · exact ⟨[1], cp_inR i n 1 (by omega) [1] rfl, rfl⟩
        · exact ⟨[2], cp_inR i n 2 (by omega) [2] rfl, rfl⟩
        · exact ⟨[3], cp_inR i n 3 (by omega) [3] rfl, rfl⟩
        · exact ⟨[4], cp_inR i n 4 (by omega) [4] rfl, rfl⟩
        · exact ⟨[5], cp_inR i n 5 (by omega) [5] rfl, rfl⟩
        · exact ⟨[6], cp_inR i n 6 (by omega) [6] rfl, rfl⟩
        · exact ⟨[7], cp_inR i n 7 (by omega) [7] rfl, rfl⟩)
    have nextNat : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
      rfl
    have rankPost : memeqByte8Rank n (evaluateHOLFiniteState current memcpyByte8Body).2 = (n.toNat - (i + 8).toNat) / 8 := by
      simp [memeqByte8Rank, li]
    exact ⟨_, by omega, by omega, Or.inl ⟨run, inv, by rw [rankPost, rankEq, nextNat]; omega⟩⟩
  obtain ⟨result, post, run, cost, remaining, out⟩ := evaluate_ranked_loop_returnsQ condition memcpyByte8Body
    (CpInv dst src n M D B G C) (memeqByte8Rank n) 0 (fun _ _ => False) guard (fun _ h => cp_dec h) (fun _ => rfl) step s hs
    (by simpa using budget)
  rw [memcpyByte8Loop_shape]
  rcases out with ⟨rfl, inv, r0⟩ | ⟨_, _, f⟩
  · exact ⟨post, run, by simpa using cost, remaining, inv, r0⟩
  · exact f.elim

theorem cp_loop1 {dst src n : BitVec 64}
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (dst + x)) ∧ D (panByteAlignHOL (src + x)))
    (s : PanSemStateFiniteExact 64 F) (hs : CpInv dst src n M D B G C s)
    (budget : memeqByteRank n s ≤ s.clock) :
    ∃ post, evaluateHOLFiniteState s memcpyByte1Loop = (none, post) ∧
      s.clock ≤ post.clock + memeqByteRank n s ∧ post.clock ≤ s.clock ∧ CpInv dst src n M D B G C post := by
  let condition : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
  have guard : ∀ current : PanSemStateFiniteExact 64 F, CpInv dst src n M D B G C current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if memeqByteRank n current = 0 then 0 else 1))) := by
    rintro current ⟨_, _, localN, ⟨i, localI, inside⟩, _⟩
    have rankEq : memeqByteRank n current = n.toNat - i.toNat := by simp [memeqByteRank, localI]
    by_cases done : i.toNat = n.toNat
    · have equal : i = n := BitVec.eq_of_toNat_eq done
      have zero : memeqByteRank n current = 0 := by rw [rankEq, done]; omega
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,equal,zero,Compiler.Encoders.Asm.wordCmpHOL]
    · have positive : memeqByteRank n current ≠ 0 := by rw [rankEq]; omega
      have below : i < n := BitVec.lt_def.mpr (by omega)
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,positive,Compiler.Encoders.Asm.wordCmpHOL,below]
  have step : ∀ current : PanSemStateFiniteExact 64 F, CpInv dst src n M D B G C current → 0 < memeqByteRank n current →
      0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memcpyByte1Body = (none,post) ∧ CpInv dst src n M D B G C post ∧
            memeqByteRank n post < memeqByteRank n current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (fun _ _ => False) result post ∧
           evaluateHOLFiniteState current memcpyByte1Body = (some result,post))) := by
    intro current hc positive _
    obtain ⟨i, localI, inside⟩ := hc.2.2.2.1
    have rankEq : memeqByteRank n current = n.toNat - i.toNat := by simp [memeqByteRank, localI]
    have below : i.toNat + 1 ≤ n.toNat := by rw [rankEq] at positive; omega
    obtain ⟨run, inv, li, ck⟩ := cp_step (show ByteAdvanceStep (ofString "i") 1 memcpyByte1Body from
        ByteAdvanceStep.store _ _ ByteAdvanceStep.advance) bsNoDec_memcpyByte1 cells current i hc localI
      (by change i.toNat + 1 ≤ n.toNat; omega) (by
        rw [bsStores_memcpyByte1]
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact ⟨[], cp_inR i n 0 (by omega) [] rfl, rfl⟩)
    have nextNat : (i + 1).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2 ^ 64; omega)]
      rfl
    have rankPost : memeqByteRank n (evaluateHOLFiniteState current memcpyByte1Body).2 = n.toNat - (i + 1).toNat := by
      simp [memeqByteRank, li]
    exact ⟨_, by omega, by omega, Or.inl ⟨run, inv, by rw [rankPost, rankEq, nextNat]; omega⟩⟩
  obtain ⟨result, post, run, cost, remaining, out⟩ := evaluate_ranked_loop_returnsQ condition memcpyByte1Body
    (CpInv dst src n M D B G C) (memeqByteRank n) 0 (fun _ _ => False) guard (fun _ h => cp_dec h) (fun _ => rfl) step s hs
    (by simpa using budget)
  rw [source_memcpy_byte1_loop]
  rcases out with ⟨rfl, inv, _⟩ | ⟨_, _, f⟩
  · exact ⟨post, run, by simpa using cost, remaining, inv⟩
  · exact f.elim

end cp
#print axioms bsStores_memcpyByte8
#print axioms cp_pair_ok
#print axioms cp_step
#print axioms cp_loop8
#print axioms cp_loop1
end InitECandidate.Runtime

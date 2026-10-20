import InitECandidate.Runtime.PtKeyURdGD
import InitECandidate.Runtime.HashSelectWidths
/-!
The unaligned branch of the source `htab_hash` for the 20/32/52-byte widths: each `LD_LE64`/`LD_LE32` word is
assembled from `ld8` loads, xored into the hash, and the final mix returns.  The branch returns a word without
consuming clocks or changing memory, globals, code, domain or endianness, needing only the aligned cells of the key's
bytes (`memaddrs (panByteAlignHOL (p + j))`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One byte-assembled hash word: `w = e; h = h ^ w; k`. -/
def kuThen (e : ExpHOL 64) (k : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "w") e)
    (.seq (.assign .local (ofString "h") (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")])) k)

/-- A hash word of the unaligned branch: an `LD_LE64` or `LD_LE32` at `kuAddr base`. -/
inductive KuW where
  | w64 (base : List (BitVec 64))
  | w32 (base : List (BitVec 64))

def KuW.exp : KuW → ExpHOL 64
  | .w64 b => kuLe64 b
  | .w32 b => kuLe32 b

def KuW.base : KuW → List (BitVec 64)
  | .w64 b => b
  | .w32 b => b

def KuW.len : KuW → Nat
  | .w64 _ => 8
  | .w32 _ => 4

def kuChain (ws : List KuW) : ProgHOL 64 := ws.foldr (fun w k => kuThen w.exp k) hashFinish

def hashU20 : ProgHOL 64 := kuChain [.w64 [], .w64 [8], .w32 [16]]
def hashU32 : ProgHOL 64 := kuChain [.w64 [], .w64 [8], .w64 [16], .w64 [24]]
def hashU52 : ProgHOL 64 := kuChain [.w64 [], .w64 [8], .w64 [16], .w64 [24], .w64 [32], .w64 [40], .w32 [48]]

/-- The literal unaligned branch of the source `htab_hash`. -/
theorem source_hash_unaligned : hashUnalignedBody =
    .seq (.ite (hashSizeCondition 20) hashU20 .skip)
      (.seq (.ite (hashSizeCondition 32) hashU32 .skip) (.ite (hashSizeCondition 52) hashU52 .skip)) := by rfl

section ev
variable {F : Type}

theorem eval_kuW (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer))) (w : KuW)
    (dom : ∀ j : Nat, j < w.len → state.memaddrs (panByteAlignHOL (pointer + kuOff w.base + BitVec.ofNat 64 j))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) w.exp = some (.val (.word v)) := by
  cases w with
  | w64 b => exact eval_kuLe64 state pointer binding b dom
  | w32 b => exact eval_kuLe32 state pointer binding b dom

theorem evaluate_kuThen (state : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (k : ProgHOL 64)
    (hash oldWord value : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) e = some (.val (.word value))) :
    evaluateHOLFiniteState state (kuThen e k) =
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
        (setVarHOLFinite (ofString "w") (.val (.word value)) state)) k := by
  have step := evaluate_hashExpressionStep state e hash oldWord value hashLocal wordLocal loaded
  change evaluateHOLFiniteState state (.seq _ (.seq _ k)) = _
  rw [← evaluate_seq_assoc]
  change evaluateHOLFiniteState state (.seq (hashExpressionStep e) k) = _
  rw [evaluateHOLFiniteState_seq_line780, step]

/-- A chain of byte-assembled hash words followed by the final mix returns a word, keeping every nonlocal field. -/
theorem evaluate_kuChain (ws : List KuW) (state : PanSemStateFiniteExact 64 F) (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (dom : ∀ w ∈ ws, ∀ j : Nat, j < w.len →
      state.memaddrs (panByteAlignHOL (pointer + kuOff w.base + BitVec.ofNat 64 j))) :
    ∃ value post, evaluateHOLFiniteState state (kuChain ws) = (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  induction ws generalizing state hash oldWord with
  | nil =>
    refine ⟨_, _, evaluate_hashFinish state hash hashLocal, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons w rest ih =>
    obtain ⟨value, loaded⟩ := eval_kuW state pointer pointerLocal w (dom w (by simp))
    let middle := setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
      (setVarHOLFinite (ofString "w") (.val (.word value)) state)
    have hp : ofString "h" ≠ ofString "p" := by decide
    have wp : ofString "w" ≠ ofString "p" := by decide
    have hw : ofString "h" ≠ ofString "w" := by decide
    have p : middle.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simp [middle, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp, wp, pointerLocal]
    have h : middle.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ value))) := by
      simp [middle, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have ww : middle.locals.lookup (ofString "w") = some (.val (.word value)) := by
      simp [middle, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw]
    obtain ⟨result, post, run, frame⟩ := ih middle (hash ^^^ value) value p h ww
      (fun x hx => dom x (List.mem_cons_of_mem w hx))
    refine ⟨result, post, ?_, frame⟩
    change evaluateHOLFiniteState state (kuThen w.exp (kuChain rest)) = _
    rw [evaluate_kuThen state w.exp (kuChain rest) hash oldWord value hashLocal wordLocal loaded]
    exact run

end ev
#print axioms source_hash_unaligned
#print axioms evaluate_kuChain
end InitECandidate.Runtime

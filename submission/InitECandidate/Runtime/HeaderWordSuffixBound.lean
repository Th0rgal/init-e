import InitECandidate.Runtime.HeaderWordLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def headerWordSizeCondition : ExpHOL 64 := .cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "f")))
def headerWordSizeGuard : ProgHOL 64 := .ite headerWordSizeCondition (.raise (ofString "HdrErr") (.const 4)) .skip

theorem source_header_word_guard : headerWordAt 1 = .seq headerWordSizeGuard (headerWordAt 2) := rfl

theorem source_header_word_value : headerWordAt 2 = .dec (ofString "v") .one (.const 0) (headerWordAt 3) := rfl

theorem source_header_word_index : headerWordAt 3 = .dec (ofString "j") .one (.const 0) (headerWordAt 4) := rfl

/-- The original size check either rejects the field or runs the actual byte
loop with at most eight ticks. The size bound is derived at the guard. -/
theorem runBounded_header_word_suffix {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer length : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atField : s.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (budget : 8 ≤ s.clock) : RunBounded s (headerWordAt 1) 8 := by
  classical
  have cond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) headerWordSizeCondition =
      some (.val (.word (if 8 < length.toNat then 1 else 0))) := by
    simp [headerWordSizeCondition,evalHOLExact,atField,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  rw [source_header_word_guard]
  have guardBound : RunBounded s headerWordSizeGuard 0 :=
    RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega)
  apply RunBounded.seq (a := 0) (b := 8) guardBound (by simpa using budget)
  intro next normal nextCode ticks
  by_cases large : 8 < length.toNat
  · have guard : evaluateHOLFiniteState s headerWordSizeGuard =
        evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 4)) := by
      unfold headerWordSizeGuard
      rw [evaluateHOLFiniteState_ite,cond]
      simp [large]
    have noNormal : (evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 4))).1 ≠ none := by
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only; split <;> simp
      · simp
    rw [guard] at normal
    exact False.elim (noNormal (congrArg Prod.fst normal))
  · have guard : evaluateHOLFiniteState s headerWordSizeGuard = (none,s) := by
      unfold headerWordSizeGuard
      rw [evaluateHOLFiniteState_ite,cond]
      simp [large,evaluateHOLFiniteState_skip]
    rw [guard] at normal
    have same : next = s := (Prod.mk.inj normal).2.symm
    subst next
    rw [source_header_word_value]
    apply RunBounded.decConst
    rw [source_header_word_index]
    apply RunBounded.decConst
    let entry := setVarHOLFinite (ofString "j") (.val (.word (0#64)))
      (setVarHOLFinite (ofString "v") (.val (.word (0#64))) s)
    have atJ : entry.locals.lookup (ofString "j") = some (.val (.word (0#64))) := by
      simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have fieldKept : entry.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
      simpa (config := {decide := true}) [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atField
    rw [source_header_word_loop]
    apply RunBounded.seq (a := 8) (b := 0)
      (runBounded_header_word_loop entry pointer length 0 code atJ fieldKept (by simp) (by omega) budget) (by change 8 ≤ s.clock; exact budget)
    intro post _ installed _
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) (installed.trans code) (by omega)

#print axioms source_header_word_guard
#print axioms runBounded_header_word_suffix
end InitECandidate.Runtime

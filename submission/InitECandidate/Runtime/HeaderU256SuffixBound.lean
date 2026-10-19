import InitECandidate.Runtime.HeaderWordLoopBound
import InitECandidate.Runtime.U256FromBeBodyBound
import InitECandidate.Runtime.OriginalU256FromBeCode
import InitECandidate.Runtime.PanTwoWordLookupShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def headerU256At (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_hdr_u256_field)
def headerU256SizeCondition : ExpHOL 64 := .cmp .lower (.const 32) (.rfield 1 (.var .local (ofString "f")))
def headerU256SizeGuard : ProgHOL 64 := .ite headerU256SizeCondition (.raise (ofString "HdrErr") (.const 5)) .skip

theorem source_header_u256_guard : headerU256At 1 = .seq headerU256SizeGuard (headerU256At 2) := rfl
theorem source_header_u256_conversion : headerU256At 2 =
    .decCall (ofString "v") (.comb [.one,.one,.one,.one]) (ofString "u256_from_be")
      [.rfield 0 (.var .local (ofString "f")),.rfield 1 (.var .local (ofString "f"))]
      (.return (.var .local (ofString "v"))) := rfl

/-- The original size check either rejects the field or runs the actual
32-byte converter. The installed conversion and return spend at most 33 ticks. -/
theorem runBounded_header_u256_suffix {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer length : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atField : s.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (budget : 33 ≤ s.clock) : RunBounded s (headerU256At 1) 33 := by
  classical
  have cond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) headerU256SizeCondition =
      some (.val (.word (if 32 < length.toNat then 1 else 0))) := by
    simp [headerU256SizeCondition,evalHOLExact,atField,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  rw [source_header_u256_guard]
  have guardBound : RunBounded s headerU256SizeGuard 0 :=
    RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega)
  apply RunBounded.seq (a := 0) (b := 33) guardBound (by simpa using budget)
  intro next normal nextCode ticks
  by_cases large : 32 < length.toNat
  · have guard : evaluateHOLFiniteState s headerU256SizeGuard =
        evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 5)) := by
      unfold headerU256SizeGuard
      rw [evaluateHOLFiniteState_ite,cond]
      simp [large]
    have noNormal : (evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 5))).1 ≠ none := by
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only; split <;> simp
      · simp
    rw [guard] at normal
    exact False.elim (noNormal (congrArg Prod.fst normal))
  · have guard : evaluateHOLFiniteState s headerU256SizeGuard = (none,s) := by
      unfold headerU256SizeGuard
      rw [evaluateHOLFiniteState_ite,cond]
      simp [large,evaluateHOLFiniteState_skip]
    rw [guard] at normal
    have same : next = s := (Prod.mk.inj normal).2.symm
    subst next
    rw [source_header_u256_conversion]
    have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.rfield 0 (.var .local (ofString "f")),.rfield 1 (.var .local (ofString "f"))] =
        some [.val (.word pointer),.val (.word length)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,atField]
    change RunBounded s _ (32 + 1 + 0)
    apply RunBounded.decCall (bodyCost := 32) (tailCost := 0) args (by omega)
    intro body callee shape lookup
    have installedLookup := pan_two_word_lookup_shape s.code.lookup (ofString "u256_from_be") (ofString "p") (ofString "n")
      (sourceFunctionBody Guest.guestFn_u256_from_be) (.comb [.one,.one,.one,.one]) pointer length (by decide)
      (by rw [code]; exact originalRuntimeCode_u256FromBe_lookup)
    rw [installedLookup] at lookup
    obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
    let entry := callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length)))
    have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have atLength : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
      simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have bounded := evaluate_u256FromBe_body_bounded entry pointer length 32 atPointer atLength code (by omega) (by omega)
      (by change 32 ≤ s.clock - 1; omega)
    refine ⟨⟨bounded.1,bounded.2.1,bounded.2.2.1⟩,?_⟩
    intro value post returned _
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_u256_from_be)
    change evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_u256_from_be) = _ at returned
    rw [returned] at metadata
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) (metadata.1.trans code) (by omega)

#print axioms source_header_u256_guard
#print axioms runBounded_header_u256_suffix
end InitECandidate.Runtime

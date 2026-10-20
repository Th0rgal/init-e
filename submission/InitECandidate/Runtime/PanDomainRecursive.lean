import InitECandidate.Runtime.PanDomainAtoms
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panDomainMono_seq {F : Type} (s : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (secondIH : ∀ result post,(result,post)=evaluateHOLFiniteState s first ∧result=none→PanDomainMonoAt second post)
    (firstIH : PanDomainMonoAt first s) : PanDomainMonoAt (.seq first second) s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_seq,fixClockHOLFinite_evaluateState] at valid ⊢
  cases run : evaluateHOLFiniteState s first with
  | mk result post =>
    have dom : post.memaddrs=s.memaddrs := by
      have metadata:=evaluateHOLFiniteState_metadata s first
      simpa only [run] using metadata.2.1
    cases result with
    | none =>
      have firstNext := firstIH domain subset (by simp only [run,ne_eq,reduceCtorEq,not_false_eq_true])
      simp only [run] at firstNext
      have secondNext := secondIH none post ⟨run.symm,rfl⟩ domain (by simpa only [dom] using subset) (by simpa only [run] using valid)
      simp only [run,firstNext]
      exact secondNext
    | some result =>
      have noerror : (some result : Option (PanSemResultExact 64))≠some .error := by simpa only [run] using valid
      have firstNext := firstIH domain subset (by simpa only [run] using noerror)
      simp only [run] at firstNext
      simp only [run,firstNext]
 theorem panDomainMono_ite {F : Type} (s : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (ih : ∀ value payload word, @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some value ∧value=.val payload ∧payload=.word word→PanDomainMonoAt (if word≠0 then yes else no) s) :
    PanDomainMonoAt (.ite condition yes no) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_ite] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) condition with
  | none => simp only [evalHOLFinite_eq_toExact] at old;simp [old] at valid
  | some value =>
    cases value with
    | rStruct fields => simp only [evalHOLFinite_eq_toExact] at old;simp [old] at valid
    | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at old;simp [old] at valid
    | val payload => cases payload with
      | word word =>
        have next:=evalHOLFinite_memaddrs_mono s domain subset condition (.val (.word word)) old
        simp only [evalHOLFinite_eq_toExact] at old next
        simp only [old] at valid ⊢
        simp only [next]
        have selected := ih (.val (.word word)) (.word word) word ⟨old,rfl,rfl⟩
        by_cases zero : word=0
        · simp only [zero,if_pos,ne_eq,not_true_eq_false,if_false] at valid selected ⊢
          exact selected domain subset valid
        · simp only [if_neg zero,ne_eq,zero,not_false_eq_true,if_true] at valid selected ⊢
          exact selected domain subset valid
 theorem panDomainMono_dec {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (ih : ∀ value,@evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) initializer=some value ∧shape=shapeOfHOLExact value→PanDomainMonoAt body {s with locals:=s.locals.update (name,value)}) :
    PanDomainMonoAt (.dec name shape initializer body) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_dec_total] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) initializer with
  | none => simp only [evalHOLFinite_eq_toExact] at old;simp [old] at valid
  | some value =>
    have next:=evalHOLFinite_memaddrs_mono s domain subset initializer value old
    simp only [evalHOLFinite_eq_toExact] at old next
    simp only [old] at valid ⊢
    simp only [next]
    by_cases shapeOk : shapeEqHOL shape (shapeOfHOLExact value)=true
    · simp only [shapeOk,if_true] at valid ⊢
      have bounded := ih value ⟨old,(shapeEqHOL_eq_true _ _).mp shapeOk⟩ domain subset valid
      change evaluateHOLFiniteState (setVarHOLFinite name value {s with memaddrs:=domain}) body= _ at bounded
      rw [bounded]
      rfl
    · simp [shapeOk] at valid
#print axioms panDomainMono_ite
#print axioms panDomainMono_dec
#print axioms panDomainMono_seq
end InitECandidate.Runtime

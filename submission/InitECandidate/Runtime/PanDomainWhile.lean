import InitECandidate.Runtime.PanDomainRecursive
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panDomainMono_while {F : Type} (s : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (body : ProgHOL 64)
    (bodyIH : ∀ word,@evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word word))→word≠0→s.clock≠0→PanDomainMonoAt body (decClockHOLFinite s))
    (loopIH : ∀ word result post,@evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word word))→word≠0→s.clock≠0→evaluateHOLFiniteState (decClockHOLFinite s) body=(result,post)→(result=none ∨result=some .continue)→PanDomainMonoAt (.while condition body) post) :
    PanDomainMonoAt (.while condition body) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_while_fixClockRewrite s condition body, evaluateHOLFiniteState_while_fixClockRewrite {s with memaddrs:=domain} condition body] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) condition with
  | none => simp only [old] at valid;exact False.elim (valid rfl)
  | some value => cases value with
    | rStruct fields => simp only [old] at valid;exact False.elim (valid rfl)
    | nStruct name fields => simp only [old] at valid;exact False.elim (valid rfl)
    | val payload => cases payload with
      | word word =>
        have next:=evalHOLFinite_memaddrs_mono s domain subset condition (.val (.word word)) old
        simp only [old] at valid ⊢
        simp only [next]
        by_cases running : word≠0
        · simp only [if_pos running] at valid ⊢
          by_cases zero : s.clock=0
          · simp only [zero,if_pos,emptyLocalsHOLFinite]
          · simp only [if_neg zero] at valid ⊢
            cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
            | mk result post =>
              have bodyNoError : result≠some .error := by
                intro bad
                simp only [run,bad] at valid
                exact valid rfl
              have bodyNext:=bodyIH word old running zero domain subset (by simpa only [run] using bodyNoError)
              simp only [run] at bodyNext
              change evaluateHOLFiniteState (decClockHOLFinite {s with memaddrs:=domain}) body= _ at bodyNext
              simp only [run,bodyNext]
              have postSubset : ∀address,post.memaddrs address→domain address := by
                have domainEq:post.memaddrs=s.memaddrs := by
                  have metadata:=evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
                  rw [run] at metadata
                  exact metadata.2.1
                simpa only [domainEq] using subset
              cases result with
              | none =>
                apply loopIH word none post old running zero run (Or.inl rfl) domain postSubset
                simpa only [run] using valid
              | some result => cases result with
                | «continue» =>
                  apply loopIH word (some .continue) post old running zero run (Or.inr rfl) domain postSubset
                  simpa only [run] using valid
                | error => exact False.elim (bodyNoError rfl)
                | «break» => rfl
                | returned value => rfl
                | exception id value => rfl
                | timeOut => rfl
                | finalFfi event => rfl
        · simp only [if_neg running]
#print axioms panDomainMono_while
end InitECandidate.Runtime

import InitECandidate.Runtime.SourceCostCrepWork
import InitECandidate.Runtime.SourceSiteMoves
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Executed Crep work indexed by the current function, with a call price per
(caller, callee) pair. Callee bodies run at the callee's index; `CrepWorkP` is
the constant-call-price instance. -/

/-- Crep function names. -/
abbrev CName := Flapjack.Basis.Pure.MlString.MlString

inductive CrepWorkF (price : CrepExpHOL 64 → Nat) (priceList : List (CrepExpHOL 64) → Nat)
    (unit prim : Nat) (callP : CName → CName → Nat) (ret : Nat) {σ : Type} :
    CName → CrepSemHOLState 64 σ → CrepProgHOL 64 → Nat → Prop where
  | skip (fn : CName) (t) : CrepWorkF price priceList unit prim callP ret fn t .skip 0
  | tick (fn : CName) (t) : CrepWorkF price priceList unit prim callP ret fn t .tick unit
  | breakStmt (fn : CName) (t label) : CrepWorkF price priceList unit prim callP ret fn t (.break label) unit
  | continueStmt (fn : CName) (t label) : CrepWorkF price priceList unit prim callP ret fn t (.continue label) unit
  | raise (fn : CName) (t code) : CrepWorkF price priceList unit prim callP ret fn t (.raise code) (prim + 1)
  | assign (fn : CName) (t name value) : CrepWorkF price priceList unit prim callP ret fn t (.assign name value) (price value)
  | storeGlob (fn : CName) (t address value) :
      CrepWorkF price priceList unit prim callP ret fn t (.storeGlob address value) (unit + price value)
  | store (fn : CName) (t address value) :
      CrepWorkF price priceList unit prim callP ret fn t (.store address value) (unit + price address + price value)
  | store32 (fn : CName) (t address value) :
      CrepWorkF price priceList unit prim callP ret fn t (.store32 address value) (unit + price address + price value)
  | storeByte (fn : CName) (t address value) :
      CrepWorkF price priceList unit prim callP ret fn t (.storeByte address value) (unit + price address + price value)
  | returnStmt (fn : CName) (t values) :
      CrepWorkF price priceList unit prim callP ret fn t (.return values) (unit + priceList values + values.length)
  | primitive (fn : CName) (t names operator args) :
      CrepWorkF price priceList unit prim callP ret fn t (.primitive names operator args) (prim + names.length + args.length)
  | shMem (fn : CName) (t operator name address) :
      CrepWorkF price priceList unit prim callP ret fn t (.shMem operator name address) (unit + price address)
  | extCall (fn : CName) (t function configuration configurationLength array arrayLength) :
      CrepWorkF price priceList unit prim callP ret fn t (.extCall function configuration configurationLength array arrayLength) unit
  | decFailure {fn : CName} {t name value body} (failed : evalCrepSemHOLExp t value = none) :
      CrepWorkF price priceList unit prim callP ret fn t (.dec name value body) (price value)
  | dec {fn : CName} {t name value body word bodyWork}
      (evaluated : evalCrepSemHOLExp t value = some word)
      (bodyRun : CrepWorkF price priceList unit prim callP ret fn { t with locals := t.locals.updateEq (name, word) } body bodyWork) :
      CrepWorkF price priceList unit prim callP ret fn t (.dec name value body) (price value + bodyWork)
  | seqNext {fn : CName} {t first second middle firstWork secondWork}
      (one : CrepWorkF price priceList unit prim callP ret fn t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (none, middle))
      (two : CrepWorkF price priceList unit prim callP ret fn middle second secondWork) :
      CrepWorkF price priceList unit prim callP ret fn t (.seq first second) (firstWork + secondWork)
  | seqStop {fn : CName} {t first second result middle firstWork}
      (one : CrepWorkF price priceList unit prim callP ret fn t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (some result, middle)) :
      CrepWorkF price priceList unit prim callP ret fn t (.seq first second) firstWork
  | iteBranch {fn : CName} {t condition yes no word branchWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word))
      (branch : CrepWorkF price priceList unit prim callP ret fn t (if word ≠ 0 then yes else no) branchWork) :
      CrepWorkF price priceList unit prim callP ret fn t (.ite condition yes no) (unit + price condition + branchWork)
  | iteInvalid {fn : CName} {t condition yes no}
      (invalid : ∀ word, evalCrepSemHOLExp t condition ≠ some (.word word)) :
      CrepWorkF price priceList unit prim callP ret fn t (.ite condition yes no) (unit + price condition)
  | whileExit {fn : CName} {t condition body}
      (exit : ∀ word, evalCrepSemHOLExp t condition = some (.word word) → word = 0) :
      CrepWorkF price priceList unit prim callP ret fn t (.while condition body) (unit + unit + unit + price condition)
  | whileTimeout {fn : CName} {t condition body word}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock = 0) :
      CrepWorkF price priceList unit prim callP ret fn t (.while condition body) (unit + unit + unit + price condition)
  | whileLoop {fn : CName} {t condition body word bodyWork result middle restWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkF price priceList unit prim callP ret fn (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (again : result = none ∨ result = some (.continue 0))
      (rest : CrepWorkF price priceList unit prim callP ret fn middle (.while condition body) restWork) :
      CrepWorkF price priceList unit prim callP ret fn t (.while condition body) (unit + unit + unit + price condition + bodyWork + restWork)
  | whileStop {fn : CName} {t condition body word bodyWork result middle}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkF price priceList unit prim callP ret fn (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (stop : result ≠ none ∧ result ≠ some (.continue 0)) :
      CrepWorkF price priceList unit prim callP ret fn t (.while condition body) (unit + unit + unit + price condition + bodyWork)
  /-- Argument failure, lookup failure, return-name rejection or timeout. -/
  | callShort {fn : CName} {t returnInfo function arguments}
      (short : arguments.mapM (evalCrepSemHOLExp t) = none ∨
        ∃ values, arguments.mapM (evalCrepSemHOLExp t) = some values ∧
          (lookupCodeFiniteHOL t.code function values values.length = none ∨
            crepReturnInfoNodupError returnInfo ∨ t.clock = 0)) :
      CrepWorkF price priceList unit prim callP ret fn t (.call returnInfo function arguments)
        (callP fn function + priceList arguments)
  | callBody {fn : CName} {t returnInfo function arguments values body locals bodyWork result post}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : ¬ crepReturnInfoNodupError returnInfo)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkF price priceList unit prim callP ret function { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (result, post))
      (unhandled : ∀ code rts handler, result = some (.exception code) →
        returnInfo ≠ some (rts, some (code, handler))) :
      CrepWorkF price priceList unit prim callP ret fn t (.call returnInfo function arguments)
        (callP fn function + priceList arguments + values.length + bodyWork +
          ret * crepCallPayloadWords result)
  | callHandler {fn : CName} {t rts code handler function arguments values body locals bodyWork post
      handlerWork}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : rts.Nodup)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkF price priceList unit prim callP ret function { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (some (.exception code), post))
      (handlerRun : CrepWorkF price priceList unit prim callP ret fn { post with locals := t.locals } handler handlerWork) :
      CrepWorkF price priceList unit prim callP ret fn t (.call (some (rts, some (code, handler))) function arguments)
        (callP fn function + priceList arguments + values.length + bodyWork + ret + handlerWork)

section
variable {price : CrepExpHOL 64 → Nat} {priceList : List (CrepExpHOL 64) → Nat} {unit prim call ret : Nat}

/-- Constant-call-price work is indexed work in every function. -/
theorem CrepWorkP.toF {σ : Type} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (work : CrepWorkP price priceList unit prim call ret t p w) :
    ∀ fn, CrepWorkF price priceList unit prim (fun _ _ => call) ret fn t p w := by
  induction work with
  | skip t => intro fn; exact .skip fn t
  | tick t => intro fn; exact .tick fn t
  | breakStmt t l => intro fn; exact .breakStmt fn t l
  | continueStmt t l => intro fn; exact .continueStmt fn t l
  | raise t c => intro fn; exact .raise fn t c
  | assign t n v => intro fn; exact .assign fn t n v
  | storeGlob t a v => intro fn; exact .storeGlob fn t a v
  | store t a v => intro fn; exact .store fn t a v
  | store32 t a v => intro fn; exact .store32 fn t a v
  | storeByte t a v => intro fn; exact .storeByte fn t a v
  | returnStmt t vs => intro fn; exact .returnStmt fn t vs
  | primitive t ns op as => intro fn; exact .primitive fn t ns op as
  | shMem t op n a => intro fn; exact .shMem fn t op n a
  | extCall t f a b c d => intro fn; exact .extCall fn t f a b c d
  | decFailure failed => intro fn; exact .decFailure failed
  | dec evaluated _ ih => intro fn; exact .dec evaluated (ih fn)
  | seqNext _ run _ ih1 ih2 => intro fn; exact .seqNext (ih1 fn) run (ih2 fn)
  | seqStop _ run ih => intro fn; exact .seqStop (ih fn) run
  | iteBranch guard _ ih => intro fn; exact .iteBranch guard (ih fn)
  | iteInvalid invalid => intro fn; exact .iteInvalid invalid
  | whileExit exit => intro fn; exact .whileExit exit
  | whileTimeout guard nonzero clock => intro fn; exact .whileTimeout guard nonzero clock
  | whileLoop guard nonzero clock _ run again _ ih1 ih2 =>
    intro fn; exact .whileLoop guard nonzero clock (ih1 fn) run again (ih2 fn)
  | whileStop guard nonzero clock _ run stop ih => intro fn; exact .whileStop guard nonzero clock (ih fn) run stop
  | callShort short => intro fn; exact .callShort short
  | @callBody t returnInfo function arguments values body locals bodyWork result post args lookup names clock
      _ run unhandled ih =>
    intro fn; exact .callBody args lookup names clock (ih function) run unhandled
  | @callHandler t rts code handler function arguments values body locals bodyWork post handlerWork args lookup
      names clock _ run _ ih1 ih2 =>
    intro fn; exact .callHandler args lookup names clock (ih1 function) run (ih2 fn)

/-- Indexed work at a call price bounded by a constant is constant-call-price work
of no smaller total. -/
theorem CrepWorkF.toP {σ : Type} {callP : CName → CName → Nat} {fn : CName} {t : CrepSemHOLState 64 σ}
    {p : CrepProgHOL 64} {w : Nat} (work : CrepWorkF price priceList unit prim (fun _ _ => call) ret fn t p w) :
    CrepWorkP price priceList unit prim call ret t p w := by
  induction work with
  | skip _ t => exact .skip t
  | tick _ t => exact .tick t
  | breakStmt _ t l => exact .breakStmt t l
  | continueStmt _ t l => exact .continueStmt t l
  | raise _ t c => exact .raise t c
  | assign _ t n v => exact .assign t n v
  | storeGlob _ t a v => exact .storeGlob t a v
  | store _ t a v => exact .store t a v
  | store32 _ t a v => exact .store32 t a v
  | storeByte _ t a v => exact .storeByte t a v
  | returnStmt _ t vs => exact .returnStmt t vs
  | primitive _ t ns op as => exact .primitive t ns op as
  | shMem _ t op n a => exact .shMem t op n a
  | extCall _ t f a b c d => exact .extCall t f a b c d
  | decFailure failed => exact .decFailure failed
  | dec evaluated _ ih => exact .dec evaluated ih
  | seqNext _ run _ ih1 ih2 => exact .seqNext ih1 run ih2
  | seqStop _ run ih => exact .seqStop ih run
  | iteBranch guard _ ih => exact .iteBranch guard ih
  | iteInvalid invalid => exact .iteInvalid invalid
  | whileExit exit => exact .whileExit exit
  | whileTimeout guard nonzero clock => exact .whileTimeout guard nonzero clock
  | whileLoop guard nonzero clock _ run again _ ih1 ih2 => exact .whileLoop guard nonzero clock ih1 run again ih2
  | whileStop guard nonzero clock _ run stop ih => exact .whileStop guard nonzero clock ih run stop
  | callShort short => exact .callShort short
  | callBody args lookup names clock _ run unhandled ih => exact .callBody args lookup names clock ih run unhandled
  | callHandler args lookup names clock _ run _ ih1 ih2 => exact .callHandler args lookup names clock ih1 run ih2

end

#print axioms CrepWorkP.toF
#print axioms CrepWorkF.toP
end InitECandidate.Runtime.FineCost

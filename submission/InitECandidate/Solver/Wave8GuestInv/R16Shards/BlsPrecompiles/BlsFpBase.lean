import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_U256Core
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_Sha256
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsInverseLeaf

/-! Shared loop combinators, `fb_memeq`, and BLS12-381 base field (`bls_fp_*`) leaf bounds on
`GuestInv` (including `fb_bls_fp_inv_raw` from `R16ArithPort.BlsInverseLeaf` and `fb_bls_fp_inv`).
Zero `LeafStatements.lean` dependency, zero `sorry`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.FastSha256
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1

/-! ### 1. Expression-bounded upward counter loop (`while i < exp { ...; i += 1 }`) -/

mutual

def expLocalsAvoided : ExpHOL 64 → ProgHOL 64 → Bool
  | .const _, _ => true
  | .var .local name, p => avoidsLocal name p
  | .rfield _ inner, p => expLocalsAvoided inner p
  | .cmp _ a b, p => expLocalsAvoided a p && expLocalsAvoided b p
  | .shift _ a b, p => expLocalsAvoided a p && expLocalsAvoided b p
  | .op _ args, p => expListLocalsAvoided args p
  | .panop _ args, p => expListLocalsAvoided args p
  | .rstruct args, p => expListLocalsAvoided args p
  | .nfield _ _, _ | .nstruct _ _, _
  | .var .global _, _ | .baseAddr, _ | .topAddr, _ | .bytesInWord, _
  | .load _ _, _ | .loadByte _, _ | .load32 _, _ => false
termination_by structural e _ => e

def expListLocalsAvoided : List (ExpHOL 64) → ProgHOL 64 → Bool
  | [], _ => true
  | e :: es, p => expLocalsAvoided e p && expListLocalsAvoided es p
termination_by structural es _ => es

end

mutual

private theorem evalHOLExact_eq_of_expLocalsAvoided {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (heq : ∀ k, avoidsLocal k p = true → s1.locals.lookup k = s2.locals.lookup k) :
    (e : ExpHOL 64) → expLocalsAvoided e p = true →
      @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) e =
      @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) e
  | .const _, _ => rfl
  | .var .local name, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact]
    exact heq name ha
  | .var .global _, ha | .nfield _ _, ha | .nstruct _ _, ha
  | .baseAddr, ha | .topAddr, ha | .bytesInWord, ha
  | .load _ _, ha | .loadByte _, ha | .load32 _, ha => by simp [expLocalsAvoided] at ha
  | .rfield idx inner, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq inner ha]
  | .cmp cop a b, ha => by
    simp only [expLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq a ha.1,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq b ha.2]
  | .shift sh a b, ha => by
    simp only [expLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq a ha.1,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq b ha.2]
  | .op bop args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
  | .panop pop args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
  | .rstruct args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
termination_by structural e => e

private theorem evalListHOLExact_eq_of_expLocalsAvoided {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (heq : ∀ k, avoidsLocal k p = true → s1.locals.lookup k = s2.locals.lookup k) :
    (es : List (ExpHOL 64)) → expListLocalsAvoided es p = true →
      @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) es =
      @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) es
  | [], _ => rfl
  | e :: es, ha => by
    simp only [expListLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalListHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq e ha.1,
      evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq es ha.2]
termination_by structural es => es

end

noncomputable def expCounterGap (op : Cmp) (i : MlS) (limitExp : ExpHOL 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) limitExp with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_up_exp_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower)
    (i : MlS) (limitExp : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hlim : expLocalsAvoided limitExp body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) limitExp) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) limitExp) body B (2 ^ 64)
    (expCounterGap op i limitExp)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [expCounterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    have hia : s.locals.lookup i = some (.val (.word a)) := by
      simpa [evalAt, evalHOLExact] using ha
    have hlim_s : @evalHOLExact 64 F _ s.toExact
        (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp =
        some (.val (.word b)) := by
      simpa [evalAt] using hb
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    have hi' := hstep (decClockHOLFinite s) a hia hflow
    have hflow' : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue :=
      hflow.elim Or.inl (fun h => Or.inr (Or.inr h))
    have hkeep : ∀ k, avoidsLocal k body = true →
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup k =
        s.locals.lookup k :=
      fun k hk => evaluate_avoidsLocal_flowing k body hk (decClockHOLFinite s) hflow'
    have hlim_eq : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        @evalHOLExact 64 F _ s.toExact
          (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp :=
      evalHOLExact_eq_of_expLocalsAvoided _ s body hkeep limitExp hlim
    have hlim' : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        some (.val (.word b)) := hlim_eq.trans hlim_s
    have hsucc := cmpRank_succ op a b hlt
    simp only [expCounterGap, hi', hlim', hia, hlim_s]
    omega

theorem tailCall_guestInv' {fname : MlS} {B : Nat} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.tailCall_guestInv hf arguments

/-! ### 2. `DomainTouch` for conditional loads and `fb_memeq` -/

private theorem eval_cmp_left_some {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : Cmp) (l r : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp c l r) = some v) :
    ∃ vl, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l = some vl := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i _ _ _ _ hl _
    exact ⟨_, hl⟩
  · simp at he

private theorem eval_load_one_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some v) :
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word a)) ∧ s.memaddrs a := by
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at he
  split at he
  · rename_i a ha
    simp only [memLoadHOLExact] at he
    split at he
    · rename_i hd
      exact ⟨a, ha, hd⟩
    · simp at he
  · simp at he

private theorem eval_loadByte_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte e) = some v) :
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word a)) ∧ s.memaddrs (panByteAlignHOL a) := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i a ha
    refine ⟨a, ha, ?_⟩
    by_contra hc
    cases hm : s.memory (panByteAlignHOL a) with
    | word _ => simp [panMemLoadByteHOL, hm, hc] at he
  · simp at he

theorem DomainTouch.ite_cmp_load (address r : ExpHOL 64) (c : Cmp) (yes no : ProgHOL 64) :
    DomainTouch address (.ite (.cmp c (.load .one address) r) yes no) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_ite] at hflow
  split at hflow
  · rename_i w hw
    obtain ⟨vl, hl⟩ := eval_cmp_left_some s c (.load .one address) r (.val (.word w)) hw
    obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s address vl hl
    rw [hguest.memaddrs] at hdom
    have hi := ordinaryDomain_interval addr hdom
    exact ⟨addr, haddr, hi.1, by omega⟩
  · simp at hflow

theorem DomainTouch.ite_cmp_loadByte (address r : ExpHOL 64) (c : Cmp) (yes no : ProgHOL 64) :
    DomainTouch address (.ite (.cmp c (.loadByte address) r) yes no) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_ite] at hflow
  split at hflow
  · rename_i w hw
    obtain ⟨vl, hl⟩ := eval_cmp_left_some s c (.loadByte address) r (.val (.word w)) hw
    obtain ⟨addr, haddr, hdom⟩ := eval_loadByte_domain s address vl hl
    rw [hguest.memaddrs] at hdom
    exact ⟨addr, haddr, ordinaryDomain_byte_interval addr hdom⟩
  · simp at hflow

theorem fb_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq» := by
  fb_unfold 18 Guest.Software.guestFn_memeq
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
        apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
        apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_memory_walk_guestInv (ofString "a") (ofString "i") 32 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.ite_cmp_load _ _ _ _ _))
            (by counter_step) rfl (by decide) (by decide)
        · exact while_memory_walk_guestInv (ofString "a") (ofString "i") 8 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.ite_cmp_load _ _ _ _ _))
            (by counter_step) rfl (by decide) (by decide)
      · exact straightOn _ rfl
    · apply TerminatingProgBoundedOn.seq_guestInv
      · exact while_memory_walk_guestInv (ofString "a") (ofString "i") 8 _
          (straightOn _ rfl)
          (DomainTouch.seq _ _ _ (DomainTouch.ite_cmp_loadByte _ _ _ _ _))
          (by counter_step) rfl (by decide) (by decide)
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_counter_guestInv .lower (Or.inr rfl) _ _ (straightOn _ rfl) (by incr_body) rfl
        · exact straightOn _ rfl
  · fb_arith K.«memeq»

/-! ### 3. Unfold/auto/arith tactics for BLS shards -/

syntax "bls_unfold " num ident : tactic
macro_rules
  | `(tactic| bls_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

syntax "bls_arith " ident : tactic
macro_rules
  | `(tactic| bls_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       first | omega | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega)))

syntax "bls_auto" : tactic
macro_rules
  | `(tactic| bls_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · bls_auto
         · bls_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · bls_auto
         · bls_auto)
      | (apply dec_guestInv; bls_auto)
      | (apply call_guestInv'; exact_fb_hyp)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · bls_auto)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · bls_auto)
      | (apply tailCall_guestInv'; exact_fb_hyp))

syntax "bls_auto_loops" : tactic
macro_rules
  | `(tactic| bls_auto_loops) => `(tactic| first
      | bls_auto
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · bls_auto_loops
         · bls_auto_loops)
      | (apply TerminatingProgBoundedOn.ite_on
         · bls_auto_loops
         · bls_auto_loops)
      | (apply dec_guestInv; bls_auto_loops)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · bls_auto_loops)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · bls_auto_loops)
      | skip)

syntax "bls_prove " num ident ident : tactic
macro_rules
  | `(tactic| bls_prove $idx $fn $k) => `(tactic|
      (bls_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · bls_auto
       · bls_arith $k))

/-! ### 4. BLS12-381 `bls_fp_*` base field leaves -/

theorem fb_bls_fp_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_zero") K.«bls_fp_is_zero» := by
  bls_prove 697 Guest.Software.guestFn_bls_fp_is_zero K.«bls_fp_is_zero»

theorem fb_bls_fp_eq :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_eq") K.«bls_fp_eq» := by
  bls_prove 698 Guest.Software.guestFn_bls_fp_eq K.«bls_fp_eq»

theorem fb_bls_fp_lt_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_lt_raw") K.«bls_fp_lt_raw» := by
  bls_prove 699 Guest.Software.guestFn_bls_fp_lt_raw K.«bls_fp_lt_raw»

theorem fb_bls_fp_add_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add_raw") K.«bls_fp_add_raw» := by
  bls_prove 700 Guest.Software.guestFn_bls_fp_add_raw K.«bls_fp_add_raw»

theorem fb_bls_fp_sub_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub_raw") K.«bls_fp_sub_raw» := by
  bls_prove 701 Guest.Software.guestFn_bls_fp_sub_raw K.«bls_fp_sub_raw»

theorem fb_bls_fp_add :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add") K.«bls_fp_add» := by
  have _ := fb_bls_fp_add_raw
  have _ := fb_bls_fp_sub_raw
  bls_prove 702 Guest.Software.guestFn_bls_fp_add K.«bls_fp_add»

theorem fb_bls_fp_sub :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub") K.«bls_fp_sub» := by
  have _ := fb_bls_fp_sub_raw
  have _ := fb_bls_fp_add_raw
  bls_prove 703 Guest.Software.guestFn_bls_fp_sub K.«bls_fp_sub»

theorem fb_bls_fp_neg :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_neg") K.«bls_fp_neg» := by
  have _ := fb_bls_fp_is_zero
  have _ := fb_bls_fp_sub_raw
  bls_prove 704 Guest.Software.guestFn_bls_fp_neg K.«bls_fp_neg»

theorem fb_bls_fp_mul :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_mul") K.«bls_fp_mul» := by
  have _ := fb_mul64x64
  have _ := fb_bls_fp_sub_raw
  bls_prove 706 Guest.Software.guestFn_bls_fp_mul K.«bls_fp_mul»

theorem fb_bls_fp_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sqr") K.«bls_fp_sqr» := by
  have _ := fb_bls_fp_mul
  bls_prove 707 Guest.Software.guestFn_bls_fp_sqr K.«bls_fp_sqr»

theorem fb_bls_fp_to_mont :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_mont") K.«bls_fp_to_mont» := by
  have _ := fb_bls_fp_mul
  bls_prove 708 Guest.Software.guestFn_bls_fp_to_mont K.«bls_fp_to_mont»

theorem fb_bls_fp_from_mont :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_mont") K.«bls_fp_from_mont» := by
  have _ := fb_bls_fp_mul
  bls_prove 709 Guest.Software.guestFn_bls_fp_from_mont K.«bls_fp_from_mont»

theorem fb_bls_fp_shr1 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_shr1") K.«bls_fp_shr1» := by
  bls_prove 710 Guest.Software.guestFn_bls_fp_shr1 K.«bls_fp_shr1»

theorem fb_bls_fp_half_can :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_half_can") K.«bls_fp_half_can» := by
  have _ := fb_bls_fp_shr1
  have _ := fb_bls_fp_add_raw
  bls_prove 711 Guest.Software.guestFn_bls_fp_half_can K.«bls_fp_half_can»

theorem fb_bls_fp_inv_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv_raw") K.«bls_fp_inv_raw» :=
  InitECandidate.Solver.Wave8GuestInv.Arith.fb_bls_fp_inv_raw

theorem fb_bls_fp_inv :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv") K.«bls_fp_inv» := by
  have _ := fb_bls_fp_inv_raw
  have _ := fb_bls_fp_mul
  bls_prove 713 Guest.Software.guestFn_bls_fp_inv K.«bls_fp_inv»

theorem fb_bls_fp_pow :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_pow") K.«bls_fp_pow» := by
  have _ := fb_bls_fp_mul
  bls_unfold 714 Guest.Software.guestFn_bls_fp_pow
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · bls_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · bls_arith K.«bls_fp_pow»

theorem fb_bls_fp_sgn0 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sgn0") K.«bls_fp_sgn0» := by
  have _ := fb_bls_fp_from_mont
  bls_prove 715 Guest.Software.guestFn_bls_fp_sgn0 K.«bls_fp_sgn0»

theorem fb_bls_fp_is_high :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_high") K.«bls_fp_is_high» := by
  have _ := fb_bls_fp_from_mont
  have _ := fb_bls_fp_lt_raw
  bls_prove 716 Guest.Software.guestFn_bls_fp_is_high K.«bls_fp_is_high»

theorem fb_bls_fp_from_be48 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_be48") K.«bls_fp_from_be48» := by
  bls_prove 717 Guest.Software.guestFn_bls_fp_from_be48 K.«bls_fp_from_be48»

theorem fb_bls_fp_to_be48 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_be48") K.«bls_fp_to_be48» := by
  have _ := fb_st_be64
  bls_prove 718 Guest.Software.guestFn_bls_fp_to_be48 K.«bls_fp_to_be48»

theorem fb_bls_fp_decode64 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_decode64") K.«bls_fp_decode64» := by
  have _ := fb_is_zero_bytes
  have _ := fb_bls_fp_from_be48
  have _ := fb_bls_fp_lt_raw
  have _ := fb_bls_fp_to_mont
  bls_prove 719 Guest.Software.guestFn_bls_fp_decode64 K.«bls_fp_decode64»

theorem fb_bls_fp_encode64 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_encode64") K.«bls_fp_encode64» := by
  have _ := fb_memzero
  have _ := fb_bls_fp_from_mont
  have _ := fb_bls_fp_to_be48
  bls_prove 720 Guest.Software.guestFn_bls_fp_encode64 K.«bls_fp_encode64»

theorem fb_bls_g1_msm_discount :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g1_msm_discount") K.«bls_g1_msm_discount» := by
  bls_prove 812 Guest.Software.guestFn_bls_g1_msm_discount K.«bls_g1_msm_discount»

theorem fb_bls_g2_msm_discount :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g2_msm_discount") K.«bls_g2_msm_discount» := by
  bls_prove 813 Guest.Software.guestFn_bls_g2_msm_discount K.«bls_g2_msm_discount»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

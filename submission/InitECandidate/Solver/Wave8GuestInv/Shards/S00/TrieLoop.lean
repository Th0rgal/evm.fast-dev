import InitECandidate.Solver.Wave8GuestInv.Shards.S00.TrieFrame

/-! Draft trie loop argument adapted from the RLP Stack no-repeat frame proof,
998817a20efa0796e7eb06992d98f332943646bc. Unverified until turbo-lean is available. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8Leaves.S00.Trie
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8Leaves.S00Spec InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound

theorem evalMeta {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s p).2.code = s.code ∧
    (evaluateHOLFiniteState s p).2.memaddrs = s.memaddrs ∧
    (evaluateHOLFiniteState s p).2.shMemaddrs = s.shMemaddrs ∧
    (evaluateHOLFiniteState s p).2.be = s.be ∧
    (evaluateHOLFiniteState s p).2.eshapes = s.eshapes ∧
    (evaluateHOLFiniteState s p).2.baseAddr = s.baseAddr ∧
    (evaluateHOLFiniteState s p).2.structs = s.structs := by
  have hm := evaluateHOLFiniteState_metadata s p
  have invariant := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨hm.1, hm.2.1, hm.2.2.2.1, hm.2.2.1, hm.2.2.2.2, invariant.2.2.2.2.1, invariant.2.2.2.2.2.1⟩


def cond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "node")) (.const 0)
def body : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_trie_walk with
  | .dec _ _ _ (.seq (.while _ b) _) => b
  | _ => .skip

def Pinv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ WordLocal (ofString "pos") s

def NodeDom {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ n : BitVec 64, s.locals.lookup (ofString "node") = some (.val (.word n)) ∧ ordinaryDomain n

def Rel : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s t => NodeDom s ∧ WordLocal (ofString "pos") s ∧ WordLocal (ofString "pos") t ∧
    t.memory = s.memory ∧ t.globals = s.globals ∧ t.ffi = s.ffi ∧
    t.topAddr = s.topAddr ∧ t.code = s.code ∧ t.memaddrs = s.memaddrs ∧
    t.shMemaddrs = s.shMemaddrs ∧ t.be = s.be ∧ t.eshapes = s.eshapes ∧
    t.baseAddr = s.baseAddr ∧ t.structs = s.structs ∧
    (∀ k, k ≠ ofString "node" → k ≠ ofString "pos" → t.locals.lookup k = s.locals.lookup k)

def trieKeyMax : Nat := 71723149827058354885847154688 - 2 ^ 64

private theorem addresses_bounds' (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ base.toNat + 8 * n := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt] <;>
          simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord] <;> omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

private theorem ordinaryDomain_bounds' (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have := addresses_bounds' _ _ x (by rw [hs]; decide) h
  rw [hs] at this
  have e1 : sourceBase = 2701131776 := by decide
  have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  omega

private theorem addresses_mod8 (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hb8 : base.toNat % 8 = 0) (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    x.toNat % 8 = 0 := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; exact hb8
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt] <;>
          simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord] <;> omega
      exact ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) (by omega) h

private theorem ordinaryDomain_mod8 (x : BitVec 64) (h : ordinaryDomain x) : x.toNat % 8 = 0 := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  exact addresses_mod8 _ _ x (by decide) (by rw [hs]; decide) h

def nodeSlot (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd ∧ a.toNat % 8 = 0 then
    (a.toNat - sourceBase) / 8 + 1
  else 0

theorem nodeSlot_lt (a : BitVec 64) : nodeSlot a < 3888119742 := by
  unfold nodeSlot
  split_ifs with h
  · have e1 : sourceBase = 2701131776 := by decide
    have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
    omega
  · decide

theorem nodeSlot_inj (a b : BitVec 64) (ha : ordinaryDomain a) (hb : ordinaryDomain b)
    (heq : nodeSlot a = nodeSlot b) : a = b := by
  have ba := ordinaryDomain_bounds' a ha
  have bb := ordinaryDomain_bounds' b hb
  have ma8 := ordinaryDomain_mod8 a ha
  have mb8 := ordinaryDomain_mod8 b hb
  have h1 : nodeSlot a = (a.toNat - sourceBase) / 8 + 1 := by
    unfold nodeSlot; rw [if_pos ⟨ba.1, by omega, ma8⟩]
  have h2 : nodeSlot b = (b.toNat - sourceBase) / 8 + 1 := by
    unfold nodeSlot; rw [if_pos ⟨bb.1, by omega, mb8⟩]
  rw [h1, h2] at heq
  have e1 : sourceBase = 2701131776 := by decide
  apply BitVec.eq_of_toNat_eq
  omega

def kappa : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin trieKeyMax := fun s =>
  match s.locals.lookup (ofString "node"), s.locals.lookup (ofString "pos") with
  | some (.val (.word a)), some (.val (.word b)) =>
      ⟨nodeSlot a * 2 ^ 64 + b.toNat, by
        have := nodeSlot_lt a; have := b.isLt; unfold trieKeyMax; omega⟩
  | _, _ => ⟨0, by decide⟩

theorem Rel_trans {F : Type} (a b c : PanSemStateFiniteExact 64 F)
    (h1 : Rel a b) (h2 : Rel b c) : Rel a c := by
  obtain ⟨nda, wa, _, m1, g1, f1, t1, c1, ma1, sh1, be1, es1, ba1, st1, k1⟩ := h1
  obtain ⟨_, _, wc, m2, g2, f2, t2, c2, ma2, sh2, be2, es2, ba2, st2, k2⟩ := h2
  exact ⟨nda, wa, wc, m2.trans m1, g2.trans g1, f2.trans f1, t2.trans t1, c2.trans c1,
    ma2.trans ma1, sh2.trans sh1, be2.trans be1, es2.trans es1, ba2.trans ba1,
    st2.trans st1, fun k hn hp => (k2 k hn hp).trans (k1 k hn hp)⟩

theorem node_of_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InitECandidate.Solver.PanTerminatingNoRepeat.LoopActive cond s) :
    WordLocal (ofString "node") s := by
  obtain ⟨w, hw, hw0⟩ := h
  simp only [cond, evalHOLFinite_eq_toExact, evalHOLExact] at hw
  rcases hn : s.locals.lookup (ofString "node") with _ | ⟨⟨n⟩⟩ | fs | ⟨nn, fs⟩ <;> simp [hn] at hw
  exact ⟨n, hn⟩

theorem nodeDom_of_flowing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s)
    (hf : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) :
    NodeDom s := by
  have hbody_eq : ∃ rest : ProgHOL 64,
      body = .dec (ofString "k") .one
        (.load .one (.op .add [.var .local (ofString "node"), .const 0])) rest := by
    dsimp only [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hbeq⟩ := hbody_eq
  rw [hbeq, evaluateHOLFiniteState_dec_total] at hf
  dsimp only at hf
  have hsome : ∃ vk, @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
      (fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
      (.load .one (.op .add [.var .local (ofString "node"), .const 0])) = some vk := by
    rcases hf with h | h
    · split at h
      · simp at h
      · exact ⟨_, by assumption⟩
    · split at h
      · simp at h
      · exact ⟨_, by assumption⟩
  obtain ⟨vk, hev⟩ := hsome
  have hload : ∃ a : BitVec 64,
      @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
        (fun x => Classical.propDecidable ((decClockHOLFinite s).memaddrs x))
        (.op .add [.var .local (ofString "node"), .const 0]) = some (.val (.word a)) ∧
      (decClockHOLFinite s).memaddrs a := by
    simp only [evalHOLExact] at hev
    split at hev
    · split at hev
      · rename_i a ha
        simp only [memLoadHOLExact] at hev
        split at hev
        · rename_i hd; exact ⟨a, ha, hd⟩
        · simp at hev
      · simp at hev
    · simp at hev
  obtain ⟨a, ha, hdom⟩ := hload
  simp only [evalHOLExact, evalListHOLExact] at ha
  rcases hn : s.locals.lookup (ofString "node") with _ | vn
  · simp [decClockHOLFinite, hn] at ha
  · rcases vn with ⟨⟨nw⟩⟩ | _ | _
    · simp [decClockHOLFinite, hn, valueIsWord, valueWord, wordOpHOL, wordOp] at ha
      subst ha
      have hdom' : s.memaddrs nw := hdom
      rw [hG.memaddrs] at hdom'
      exact ⟨nw, hn, hdom'⟩
    · simp [decClockHOLFinite, hn, valueIsWord] at ha
    · simp [decClockHOLFinite, hn, valueIsWord] at ha

theorem body_avoids (k : MlS) (hn : k ≠ ofString "node") (hp : k ≠ ofString "pos") :
    avoidsLocal k body = true := by
  simp [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    avoidsLocal, beq_iff_eq, Ne.symm hn, Ne.symm hp]

theorem step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hP : Pinv s)
    (hf : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) :
    Pinv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
      Rel s (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  have hPd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hP.1
  have hnd := nodeDom_of_flowing s hP.1 hf
  have wp := evaluate_wordLocal (ofString "pos") body rfl (decClockHOLFinite s) hP.2
    (hf.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have fr := evaluate_ro good good_ro body rfl (decClockHOLFinite s) hc
  have mt := evalMeta (decClockHOLFinite s) body
  refine ⟨⟨guestInv_evaluate _ body hPd, wp⟩, hnd, hP.2, wp, fr.1, fr.2.1, fr.2.2.1,
    fr.2.2.2, mt.1, mt.2.1, mt.2.2.1, mt.2.2.2.1, mt.2.2.2.2.1,
    mt.2.2.2.2.2.1, mt.2.2.2.2.2.2, ?_⟩
  intro k hn hp
  exact evaluate_avoidsLocal_flowing k body (body_avoids k hn hp) (decClockHOLFinite s)
    (hf.elim Or.inl (fun h => Or.inr (Or.inr h)))

def bodyK : Nat := Nat.max (K.«mpt_fail» + 1) 0 +
  Nat.max (Nat.max (K.«memeq» + 1) 0) 0 + Nat.max (K.«memeq» + 1) 0

theorem body_bound
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») :
    TerminatingProgBoundedOn GuestInv body bodyK := by
  apply TerminatingProgBoundedOn.weaken'
  · dsimp only [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    fb_auto
  · unfold bodyK
    simp only [nat_max_eq]
    omega

/-- Custom pigeonhole induction for `trie_walk`: if `b` is a non-timeout active head with
`Rel a b` and `kappa a = kappa b`:
* Either `b`'s body errors/terminates without flowing (0 further iterations), OR
* `b`'s body flows, so `NodeDom b` ALSO holds (`nb ∈ ordinaryDomain`), whence `nodeSlot na = nodeSlot nb`
  implies `na = nb`, so `b = { a with clock := b.clock }`, contradicting `evaluate_ne_of_clock_lt`!
Hence at most `trieKeyMax + 1` active heads can occur (`≤ trieKeyMax` flowing + at most `1`
non-flowing out-of-domain head), giving `(trieKeyMax + 1 + 1) * (bodyK + 1) = (71723149827058354885847154688 + 1) * (bodyK + 1)`! -/
private def VisitedDomHeads {F : Type} (state : PanSemStateFiniteExact 64 F)
    (visited : Finset (Fin trieKeyMax)) : Prop :=
  ∀ k ∈ visited, ∃ earlier : PanSemStateFiniteExact 64 F,
    kappa earlier = k ∧ Rel earlier state ∧
    InitECandidate.Solver.PanTerminatingNoRepeat.LoopActive cond earlier ∧
    state.clock < earlier.clock ∧
    evaluateHOLFiniteState earlier (.while cond body) =
      evaluateHOLFiniteState state (.while cond body)

private theorem rel_key_dom {F : Type} (a b : PanSemStateFiniteExact 64 F)
    (hR : Rel a b) (hnd_b : NodeDom b) (hk : kappa a = kappa b) :
    b = { a with clock := b.clock } := by
  obtain ⟨⟨na, hna, hdom_a⟩, ⟨pa, hpa⟩, ⟨pb, hpb⟩, m1, g1, f1, t1, c1, ma1, sh1, be1, es1, ba1, st1, k1⟩ := hR
  obtain ⟨nb, hnb, hdom_b⟩ := hnd_b
  simp only [kappa, hna, hpa, hnb, hpb, Fin.mk.injEq] at hk
  have := pa.isLt; have := pb.isLt
  have hslot : nodeSlot na = nodeSlot nb := by omega
  have ep : pa.toNat = pb.toNat := by omega
  have hna_eq : na = nb := nodeSlot_inj na nb hdom_a hdom_b hslot
  have hloc : b.locals = a.locals := by
    apply Flapjack.HolFiniteMapExact.ext_lookup
    intro k
    by_cases kn : k = ofString "node"
    · subst kn; rw [hna, hnb, hna_eq]
    by_cases kp : k = ofString "pos"
    · subst kp; rw [hpa, hpb, BitVec.eq_of_toNat_eq ep]
    exact k1 k kn kp
  cases a; cases b
  simp only at m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc ⊢
  subst m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc
  rfl

private theorem while_trie_aux
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin trieKeyMax)),
      state.code = originalRuntimeCode → Pinv state → trieKeyMax ≤ visited.card + n →
      VisitedDomHeads state visited →
      TerminatingRunBounded state (.while cond body) ((n + 1) * (bodyK + 1)) := by
  have hbb : TerminatingProgBoundedOn GuestInv body bodyK := body_bound hm hf
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hb := hbb (decClockHOLFinite state) hcode
            (guestInv_congr (s := state) rfl rfl rfl rfl hP.1)
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          have hno_flow : ¬ (result = none ∨ result = some .continue) := by
            intro hflow
            have hnd_s : NodeDom state := nodeDom_of_flowing state hP.1 (by rwa [hrun])
            have hfresh : kappa state ∉ visited := by
              intro hmem
              obtain ⟨earlier, hk, hR, _, hlt, hsame⟩ := hvis _ hmem
              have heq := rel_key_dom earlier state hR hnd_s hk
              exact InitECandidate.Solver.PanTerminatingNoRepeat.evaluate_ne_of_clock_lt
                _ state earlier (by rw [heq]) hlt hsame hnt0
            have hle : (insert (kappa state) visited).card ≤ trieKeyMax := by
              simpa using Finset.card_le_univ (insert (kappa state) visited)
            rw [Finset.card_insert_of_notMem hfresh] at hle
            omega
          simp only [hrun] at hnt hb ⊢
          cases result with
          | none => exact absurd (Or.inl rfl) hno_flow
          | some r =>
            cases r with
            | «continue» => exact absurd (Or.inr rfl) hno_flow
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + bodyK at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : InitECandidate.Solver.PanTerminatingNoRepeat.LoopActive cond state :=
            ⟨word, hword, hzero⟩
          have hb := hbb (decClockHOLFinite state) hcode
            (guestInv_congr (s := state) rfl rfl rfl rfl hP.1)
          have hunfold := InitECandidate.Solver.PanTerminatingNoRepeat.while_unfold_continue
            cond body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while cond body)).2.clock +
                (n + 1 + 1) * (bodyK + 1) ∧
              (evaluateHOLFiniteState post (.while cond body)).2.clock ≤ state.clock := by
            have hflow' : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = none ∨
                (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue := by
              rwa [hrun]
            have hnd_s : NodeDom state := nodeDom_of_flowing state hP.1 hflow'
            have hfresh : kappa state ∉ visited := by
              intro hmem
              obtain ⟨earlier, hk, hR, _, hlt, hsame⟩ := hvis _ hmem
              have heq := rel_key_dom earlier state hR hnd_s hk
              exact InitECandidate.Solver.PanTerminatingNoRepeat.evaluate_ne_of_clock_lt
                _ state earlier (by rw [heq]) hlt hsame hnt0
            obtain ⟨hPpost, hRpost⟩ := step state hcode hP hflow'
            rw [hrun] at hPpost hRpost
            dsimp only at hPpost hRpost
            have hsame := hunfold hflow'
            rw [hrun] at hsame; dsimp only at hsame
            have hsafe : result ≠ some .timeOut := by rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb (by rw [hrun]; exact hsafe)
            rw [hrun] at hspent hkept
            change state.clock - 1 ≤ post.clock + bodyK at hspent
            change post.clock ≤ state.clock - 1 at hkept
            have hmeta' : post.code = state.code := by rw [hrun] at hmeta; exact hmeta
            have hntPost : (evaluateHOLFiniteState post (.while cond body)).1 ≠ some .timeOut := by
              rw [← hsame]; exact hnt0
            obtain ⟨htail, htailKept⟩ := ih post (insert (kappa state) visited)
              (hmeta'.trans hcode) hPpost
              (by rw [Finset.card_insert_of_notMem hfresh]; omega)
              (by
                intro k hk
                rcases Finset.mem_insert.mp hk with rfl | hk
                · exact ⟨state, rfl, hRpost, hact, by omega, hsame⟩
                · obtain ⟨earlier, hke, hRe, hactE, hlt, hsameE⟩ := hvis k hk
                  exact ⟨earlier, hke, Rel_trans _ _ _ hRe hRpost, hactE, by omega,
                    hsameE.trans hsame⟩)
              hntPost
            have hmul : (n + 1) * (bodyK + 1) + (bodyK + 1) = (n + 1 + 1) * (bodyK + 1) := by
              exact (Nat.succ_mul (n + 1) (bodyK + 1)).symm
            exact ⟨by omega, by omega⟩
          simp only [hrun] at hnt hb ⊢
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + bodyK at hspent
              change post.clock ≤ state.clock - 1 at hkept
              have hone : bodyK + 1 ≤ (n + 1 + 1) * (bodyK + 1) :=
                Nat.le_mul_of_pos_left _ (by omega)
              simp only
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem loop_bound
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») :
    TerminatingProgBoundedOn Pinv (.while cond body)
      ((71723149827058354885847154688 + 1) * (bodyK + 1)) := by
  intro F state hcode hP
  have h := while_trie_aux hm hf trieKeyMax state ∅ hcode hP (by simp) (by simp [VisitedDomHeads])
  have heq : trieKeyMax + 1 ≤ 71723149827058354885847154688 + 1 := by
    unfold trieKeyMax; decide
  exact h.weaken (Nat.mul_le_mul_right _ heq)

theorem dec_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (name : MlS)
    (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      shapeEqHOL .one (shapeOfHOLExact v) = true → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ hsh
      have hb := hbody (setVarHOLFinite name val state) hcode (hQ state val hPs hsh) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem seq_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64}
    {a b : Nat} (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P Q first)
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp)) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem setVar_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (v : ValueHOL 64)
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : WordLocal name (setVarHOLFinite name v s) := by
  obtain ⟨w, rfl⟩ := shape_one_word v (by
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact])
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩


end InitECandidate.Solver.Wave8Leaves.S00.Trie

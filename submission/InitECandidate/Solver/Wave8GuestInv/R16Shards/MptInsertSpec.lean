import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfInsertIntoLeaf
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfSplitExtension

/-! Proof of `mpt_insert_node_spec` (`ContractParts/C00.lean:247`) with 0 `sorry` and 0 custom axioms.
Imported by `ContractParts/C00.lean`, so stays strictly below `ContractParts/C00..C07`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim `MptReady`, `MptInsertReady`, `MptExit` definitions (`rfl`-identical to `C00.lean`) -/

def MptReady_spec : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧ ∃ Nd, NodeHeap s Nd ∧
    RootIn Nd (locN s "node") ∧
    KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level") ∧
    locN s "klen" ≤ 64

def MptInsertReady_spec : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptReady_spec s ∧ locN s "vlen" < 2 ^ 40

def MptExit_spec : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k) ∧
    ∃ Nd Nd', NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ NodeHeap post Nd' ∧
      RootIn Nd' w.toNat ∧
      FrameOutside s post
        ((Nd.map fun n => nodeIvl s n) ++
          [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

theorem lookup__mpt_insert_node :
    originalRuntimeCode.lookup (ofString "_mpt_insert_node") =
      some ([(ofString "node", .one), (ofString "key", .one), (ofString "klen", .one),
             (ofString "level", .one), (ofString "vptr", .one), (ofString "vlen", .one)],
        sourceFnBody Guest.Software.guestFn__mpt_insert_node, .one) :=
  lookup_of_guestAst_getElem 275 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__mpt_insert_node) rfl

/-! ## 2. Parent slot & loop invariant `InsLoopInv` -/

/-- Valid parent slot in `Nd` (extension child `+48` or branch child `+32 + 8*i`, `i < 16`). -/
def ValidSlot {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (slot : Nat) : Prop :=
  ∃ p ∈ Nd,
    (memW s p = 2 ∧ slot = p + 48) ∨
    (memW s p = 3 ∧ ∃ i, i < 16 ∧ slot = p + 32 + 8 * i)

theorem ValidSlot.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat}
    {slot : Nat} (hst : NodeStep s post Nd Nd') (hv : ValidSlot s Nd slot) :
    ValidSlot post Nd' slot := by
  obtain ⟨p, hp, hkind⟩ := hv
  refine ⟨p, hst.sub p hp, ?_⟩
  rw [hst.kinds p hp]
  exact hkind

/-- Storing a typed root `wr` (`RootIn Nd wr.toNat`) into a `ValidSlot s Nd wslot.toNat`
succeeds in `s.memaddrs` and yields a `NodeStep s { s with memory := updW s.memory wslot wr } Nd Nd`. -/
theorem validSlot_store_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat} {wslot wr : BitVec 64}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hslot : ValidSlot s Nd wslot.toNat) (hr : RootIn Nd wr.toNat) :
    s.memaddrs wslot ∧
    NodeStep s { s with memory := Wave8Contracts.M26.updW s.memory wslot wr } Nd Nd := by
  obtain ⟨p, hp_in, ⟨hk2, hsl_eq⟩ | ⟨hk3, i, hi_lt, hsl_eq⟩⟩ := hslot
  · -- Extension child `+48`
    have hp := hNd.1 p hp_in
    have hins := hp.2.2.1
    have hsz : nodeSize (memW s p) = 56 := by simp [nodeSize, hk2]
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hlt64 : p + 48 < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have hwslot_bv : wslot = BitVec.ofNat 64 (p + 48) := by
      apply BitVec.eq_of_toNat_eq
      rw [hsl_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hdom : s.memaddrs wslot := by
      obtain ⟨_, hd, _⟩ := hp.2.2.2.1.2.2 6 (by dsimp [nodeIvl]; omega)
      dsimp [nodeIvl] at hd
      rwa [hwslot_bv]
    set m1 := Wave8Contracts.M26.updW s.memory wslot wr
    set post : PanSemStateFiniteExact 64 F := { s with memory := m1 }
    have hmw_other : ∀ off : Nat, off ≤ 40 → memW post (p + off) = memW s (p + off) := by
      intro off hoff
      have hlt : p + off < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
      have hne : BitVec.ofNat 64 (p + off) ≠ wslot := by
        intro heq; have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hsl_eq] at this; omega
      unfold memW
      change (match m1 (BitVec.ofNat 64 (p + off)) with | .word w => w.toNat) = _
      simp [m1, Wave8Contracts.M26.updW, if_neg hne]
    have hmw_48 : memW post (p + 48) = wr.toNat := by
      unfold memW
      change (match m1 (BitVec.ofNat 64 (p + 48)) with | .word w => w.toNat) = _
      rw [← hwslot_bv]; simp [m1, Wave8Contracts.M26.updW]
    refine ⟨hdom, nodeStep_modify_node ha hNd hp_in rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · intro a hout
      by_cases ha_eq : a = wslot
      · exfalso; apply hout; rw [ha_eq, hsl_eq, hsz]; omega
      · simp [post, m1, Wave8Contracts.M26.updW, if_neg ha_eq]
    · intro _; rw [hmw_48]; exact hr
    · rw [hk2]; intro h; cases h
    · intro _; exact ⟨hmw_other 32 (by decide), hmw_other 40 (by decide)⟩
    · rw [hmw_other 16 (by decide)]; exact hp.2.2.2.2.2.2.2.1
    · rw [hk2]; intro h; cases h
    · rw [hk2]; intro h; cases h
  · -- Branch child `+32 + 8*i`
    have hp := hNd.1 p hp_in
    have hins := hp.2.2.1
    have hsz : nodeSize (memW s p) = 176 := by simp [nodeSize, hk3]
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hp_lt : p < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have hsl_lt : p + 32 + 8 * i < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have hwslot_eq : wslot = BitVec.ofNat 64 p + BitVec.ofNat 64 32 + BitVec.ofNat 64 i * BitVec.ofNat 64 8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [hsl_eq, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hp_nat : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt]
    have hi_nat : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨hdom_b, hstep_b, _⟩ := branch_store_child_step (br := BitVec.ofNat 64 p) (idx := BitVec.ofNat 64 i) (wch := wr)
      ha hNd (by rw [hp_nat]; exact hp_in) (by rw [hp_nat]; exact hk3) (by rw [hi_nat]; exact hi_lt) hr
    rw [← hwslot_eq] at hdom_b hstep_b
    exact ⟨hdom_b, hstep_b⟩

/-- Loop invariant for `_mpt_insert_node`:
tracks word bindings for all loop-active locals, `NodeStep s0 s Nd0 Nd`, `RootIn Nd result`,
and when `go ≠ 0` the active descent invariant (`level ≤ klen`, `RootIn Nd node`, `KeyIn`, `ValidSlot`). -/
def InsLoopInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (Nd0 : List Nat)
    (wkey wklen wvptr wvlen : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.locals.lookup (ofString "key") = some (.val (.word wkey)) ∧
  s.locals.lookup (ofString "klen") = some (.val (.word wklen)) ∧
  s.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) ∧
  s.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) ∧
  wvlen.toNat < 2 ^ 40 ∧
  wklen.toNat ≤ 64 ∧
  ∃ (wnode wslot wlevel wres wgo : BitVec 64) (Nd : List Nat),
    s.locals.lookup (ofString "node") = some (.val (.word wnode)) ∧
    s.locals.lookup (ofString "slot") = some (.val (.word wslot)) ∧
    s.locals.lookup (ofString "level") = some (.val (.word wlevel)) ∧
    s.locals.lookup (ofString "result") = some (.val (.word wres)) ∧
    s.locals.lookup (ofString "go") = some (.val (.word wgo)) ∧
    NodeStep s0 s Nd0 Nd ∧
    RootIn Nd wres.toNat ∧
    (wgo ≠ 0 →
      wlevel.toNat ≤ wklen.toNat ∧
      RootIn Nd wnode.toNat ∧
      KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat) ∧
      (wslot = 0 ∨ (ValidSlot s Nd wslot.toNat ∧ wres.toNat ∈ Nd)))

theorem InsLoopInv.decClock {F : Type} {s0 s : PanSemStateFiniteExact 64 F} {Nd0 : List Nat}
    {wkey wklen wvptr wvlen : BitVec 64}
    (h : InsLoopInv s0 Nd0 wkey wklen wvptr wvlen s) :
    InsLoopInv s0 Nd0 wkey wklen wvptr wvlen (decClockHOLFinite s) := by
  obtain ⟨hc, hk, hkl, hvp, hvl, hvlt, hklt, wnode, wslot, wlevel, wres, wgo, Nd,
    hnd, hsl, hlv, hrs, hgo, hstep, hr_res, hact⟩ := h
  refine ⟨hc, hk, hkl, hvp, hvl, hvlt, hklt, wnode, wslot, wlevel, wres, wgo, Nd,
    hnd, hsl, hlv, hrs, hgo, hstep.with_locals_clock s.locals (s.clock - 1), hr_res, ?_⟩
  intro hgo_nz
  exact hact hgo_nz

/-! ## 3. Shared tail helper (`if slot == 0 { result = r } else { st slot, r }; node = ...`) -/

def insFinishProg : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
      (.assign .local (ofString "result") (.var .local (ofString "r")))
      (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))))
    (.seq
      (.assign .local (ofString "node") (.var .local (ofString "next_node")))
      (.seq
        (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
        (.assign .local (ofString "level") (.var .local (ofString "next_level")))))

theorem insFinish_step {F : Type}
    {s0 u t : PanSemStateFiniteExact 64 F} {Nd0 Nd : List Nat}
    {wkey wklen wvptr wvlen wslot wres wr wnn wns wnl wgo : BitVec 64}
    (ha0 : ArenaReady s0)
    (hstep : NodeStep s0 u Nd0 Nd)
    (huc : u.code = originalRuntimeCode)
    (hukey : u.locals.lookup (ofString "key") = some (.val (.word wkey)))
    (huklen : u.locals.lookup (ofString "klen") = some (.val (.word wklen)))
    (huvptr : u.locals.lookup (ofString "vptr") = some (.val (.word wvptr)))
    (huvlen : u.locals.lookup (ofString "vlen") = some (.val (.word wvlen)))
    (hvlt : wvlen.toNat < 2 ^ 40)
    (hklt : wklen.toNat ≤ 64)
    (huslot : u.locals.lookup (ofString "slot") = some (.val (.word wslot)))
    (hures : u.locals.lookup (ofString "result") = some (.val (.word wres)))
    (hur : u.locals.lookup (ofString "r") = some (.val (.word wr)))
    (hunn : u.locals.lookup (ofString "next_node") = some (.val (.word wnn)))
    (huns : u.locals.lookup (ofString "next_slot") = some (.val (.word wns)))
    (hunl : u.locals.lookup (ofString "next_level") = some (.val (.word wnl)))
    (hugo : u.locals.lookup (ofString "go") = some (.val (.word wgo)))
    (hr_root : RootIn Nd wr.toNat)
    (hslot_inv : wslot = 0 ∨ (ValidSlot u Nd wslot.toNat ∧ wres.toNat ∈ Nd))
    (hnext_inv : wgo ≠ 0 →
      wnl.toNat ≤ wklen.toNat ∧
      RootIn Nd wnn.toNat ∧
      KeyIn u Nd (wkey.toNat + wnl.toNat) (wklen.toNat - wnl.toNat) ∧
      ValidSlot u Nd wns.toNat ∧
      wns ≠ 0 ∧
      wr.toNat ∈ Nd)
    (hrun : evaluateHOLFiniteState u insFinishProg = (none, t)) :
    InsLoopInv s0 Nd0 wkey wklen wvptr wvlen t := by
  dsimp only [insFinishProg] at hrun
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases h1 : evaluateHOLFiniteState u
      (.ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
        (.assign .local (ofString "result") (.var .local (ofString "r")))
        (.store (.var .local (ofString "slot")) (.var .local (ofString "r")))) with ⟨r1, u1⟩
  rw [h1] at hrun
  cases r1 with
  | some _ => simp at hrun
  | none =>
    dsimp only at hrun
    have hc_slot : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .equal (.var .local (ofString "slot")) (.const 0)) =
        some (.val (.word (if wslot = 0 then 1 else 0))) := by
      simp [evalHOLExact, huslot, Compiler.Encoders.Asm.wordCmpHOL]
    have hu1_facts : ∃ wres' : BitVec 64,
        NodeStep u u1 Nd Nd ∧
        u1.code = originalRuntimeCode ∧
        RootIn Nd wres'.toNat ∧
        (wgo ≠ 0 → wres'.toNat ∈ Nd) ∧
        u1.locals.lookup (ofString "result") = some (.val (.word wres')) ∧
        (∀ x : MlS, x ≠ ofString "result" → u1.locals.lookup x = u.locals.lookup x) := by
      by_cases hsl0 : wslot = 0
      · rw [evaluateHOLFiniteState_ite, hc_slot, if_pos hsl0] at h1
        simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at h1
        rw [evaluateHOLFiniteState_assign] at h1
        have hur_ev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.var .local (ofString "r")) = some (.val (.word wr)) := hur
        rw [hur_ev] at h1
        dsimp only at h1
        split at h1
        · injection h1 with _ hu1_eq
          subst hu1_eq
          refine ⟨wr, (NodeStep.refl hstep.arena hstep.heap).with_locals_clock _ _, huc, hr_root,
            fun hgz => (hnext_inv hgz).2.2.2.2.2,
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            fun x hx => by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]⟩
        · simp at h1
      · obtain ⟨hvslot, hwres_in⟩ := hslot_inv.resolve_left hsl0
        obtain ⟨hdom_sl, hst_sl⟩ := validSlot_store_step hstep.arena hstep.heap hvslot hr_root
        rw [evaluateHOLFiniteState_ite, hc_slot] at h1
        simp only [hsl0, ↓reduceIte] at h1
        rw [evaluateHOLFiniteState_store] at h1
        have husl_ev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.var .local (ofString "slot")) = some (.val (.word wslot)) := huslot
        have hur_ev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.var .local (ofString "r")) = some (.val (.word wr)) := hur
        rw [husl_ev, hur_ev] at h1
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_sl, ↓reduceIte] at h1
        injection h1 with _ hu1_eq
        subst hu1_eq
        exact ⟨wres, hst_sl, huc, Or.inr hwres_in, fun _ => hwres_in, hures, fun _ _ => rfl⟩
    obtain ⟨wres', hstep_u1, hu1_c, hres'_root, hres'_in, hu1_res, hu1_other⟩ := hu1_facts
    -- Now step through the 3 local assignments: `node := next_node; slot := next_slot; level := next_level`
    have hu1_nn : u1.locals.lookup (ofString "next_node") = some (.val (.word wnn)) :=
      (hu1_other _ (by decide)).trans hunn
    have hu1_ns : u1.locals.lookup (ofString "next_slot") = some (.val (.word wns)) :=
      (hu1_other _ (by decide)).trans huns
    have hu1_nl : u1.locals.lookup (ofString "next_level") = some (.val (.word wnl)) :=
      (hu1_other _ (by decide)).trans hunl
    -- Helper to invert `.assign .local x e = (none, next)` when `e` evaluates to `w`
    have assign_inv : ∀ {st st' : PanSemStateFiniteExact 64 F} {x : String} { src : String } {w : BitVec 64},
        st.locals.lookup (ofString src) = some (.val (.word w)) →
        evaluateHOLFiniteState st (.assign .local (ofString x) (.var .local (ofString src))) = (none, st') →
        st' = setVarHOLFinite (ofString x) (.val (.word w)) st := by
      intro st st' x src w hlk hass
      rw [evaluateHOLFiniteState_assign] at hass
      have hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.var .local (ofString src)) = some (.val (.word w)) := hlk
      rw [hev] at hass; dsimp only at hass
      split at hass
      · injection hass with _ heq; exact heq.symm
      · simp at hass
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    rcases h2 : evaluateHOLFiniteState u1
        (.assign .local (ofString "node") (.var .local (ofString "next_node"))) with ⟨r2, u2⟩
    rw [h2] at hrun
    cases r2 with
    | some _ => simp at hrun
    | none =>
      dsimp only at hrun
      have hu2_eq := assign_inv hu1_nn h2
      subst hu2_eq
      set u2 := setVarHOLFinite (ofString "node") (.val (.word wnn)) u1
      have hu2_ns : u2.locals.lookup (ofString "next_slot") = some (.val (.word wns)) := by
        simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_ns,
          show ofString "node" ≠ ofString "next_slot" by decide]
      rw [evaluateHOLFiniteState_seq_line780] at hrun
      rcases h3 : evaluateHOLFiniteState u2
          (.assign .local (ofString "slot") (.var .local (ofString "next_slot"))) with ⟨r3, u3⟩
      rw [h3] at hrun
      cases r3 with
      | some _ => simp at hrun
      | none =>
        dsimp only at hrun
        have hu3_eq := assign_inv hu2_ns h3
        subst hu3_eq
        set u3 := setVarHOLFinite (ofString "slot") (.val (.word wns)) u2
        have hu3_nl : u3.locals.lookup (ofString "next_level") = some (.val (.word wnl)) := by
          simp [u3, u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_nl,
            show ofString "slot" ≠ ofString "next_level" by decide,
            show ofString "node" ≠ ofString "next_level" by decide]
        have ht_eq := assign_inv hu3_nl hrun
        subst ht_eq
        set tf := setVarHOLFinite (ofString "level") (.val (.word wnl)) u3
        have hstep_tf : NodeStep s0 tf Nd0 Nd :=
          (NodeStep.trans ha0 hstep hstep_u1).with_locals_clock tf.locals tf.clock
        have htf_other : ∀ x : MlS,
            x ≠ ofString "level" → x ≠ ofString "slot" → x ≠ ofString "node" → x ≠ ofString "result" →
            tf.locals.lookup x = u.locals.lookup x := by
          intro x h1 h2 h3 h4
          simp [tf, u3, u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm h1, Ne.symm h2, Ne.symm h3, hu1_other x h4]
        refine ⟨hu1_c,
          (htf_other _ (by decide) (by decide) (by decide) (by decide)).trans hukey,
          (htf_other _ (by decide) (by decide) (by decide) (by decide)).trans huklen,
          (htf_other _ (by decide) (by decide) (by decide) (by decide)).trans huvptr,
          (htf_other _ (by decide) (by decide) (by decide) (by decide)).trans huvlen,
          hvlt, hklt,
          wnn, wns, wnl, wres', wgo, Nd,
          by simp [tf, u3, u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
               show ofString "level" ≠ ofString "node" by decide,
               show ofString "slot" ≠ ofString "node" by decide],
          by simp [tf, u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
               show ofString "level" ≠ ofString "slot" by decide],
          by simp [tf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          by simp [tf, u3, u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_res,
               show ofString "level" ≠ ofString "result" by decide,
               show ofString "slot" ≠ ofString "result" by decide,
               show ofString "node" ≠ ofString "result" by decide],
          (htf_other _ (by decide) (by decide) (by decide) (by decide)).trans hugo,
          hstep_tf, hres'_root, ?_⟩
        intro hgo_nz
        obtain ⟨hnl_le, hnn_root, hkey_u, hvns, hwns_nz, _⟩ := hnext_inv hgo_nz
        have hstep_u_tf : NodeStep u tf Nd Nd := hstep_u1.with_locals_clock tf.locals tf.clock
        exact ⟨hnl_le, hnn_root,
          hstep_u_tf.keyIn hstep.arena hstep.heap hkey_u,
          Or.inr ⟨hvns.mono hstep_u_tf, hres'_in hgo_nz⟩⟩


/-! ## 4. AST Decomposition & Call Inversion Helpers for `_mpt_insert_node` -/

theorem InsLoopInv.restore_local {F : Type} {s0 u : PanSemStateFiniteExact 64 F} {Nd0 : List Nat}
    {wkey wklen wvptr wvlen : BitVec 64} {x : String} {old : Option (ValueHOL 64)}
    (h : InsLoopInv s0 Nd0 wkey wklen wvptr wvlen u)
    (hne : ∀ m ∈ ["key", "klen", "vptr", "vlen", "node", "slot", "level", "result", "go"],
      ofString m ≠ ofString x) :
    InsLoopInv s0 Nd0 wkey wklen wvptr wvlen
      { u with locals := HolFiniteMapExact.resVarEq u.locals (ofString x, old) } := by
  obtain ⟨hc, hk, hkl, hvp, hvl, hvlt, hklt, wnode, wslot, wlevel, wres, wgo, Nd,
    hnd, hsl, hlv, hrs, hgo, hstep, hr_res, hact⟩ := h
  have hlk (m : String) (hm : m ∈ ["key", "klen", "vptr", "vlen", "node", "slot", "level", "result", "go"]) :
      (HolFiniteMapExact.resVarEq u.locals (ofString x, old)).lookup (ofString m) =
        u.locals.lookup (ofString m) :=
    resVarEq_lookup_ne u.locals (ofString x) (ofString m) old (hne m hm)
  exact ⟨hc,
    (hlk "key" (by simp)).trans hk,
    (hlk "klen" (by simp)).trans hkl,
    (hlk "vptr" (by simp)).trans hvp,
    (hlk "vlen" (by simp)).trans hvl,
    hvlt, hklt,
    wnode, wslot, wlevel, wres, wgo, Nd,
    (hlk "node" (by simp)).trans hnd,
    (hlk "slot" (by simp)).trans hsl,
    (hlk "level" (by simp)).trans hlv,
    (hlk "result" (by simp)).trans hrs,
    (hlk "go" (by simp)).trans hgo,
    hstep.with_locals_clock _ u.clock,
    hr_res,
    hact⟩

def insDecBody : ProgHOL 64 → ProgHOL 64 | .dec _ _ _ p => p | _ => .skip
def insLeft : ProgHOL 64 → ProgHOL 64 | .seq a _ => a | _ => .skip
def insRight : ProgHOL 64 → ProgHOL 64 | .seq _ b => b | _ => .skip
def insWhileBody : ProgHOL 64 → ProgHOL 64 | .while _ b => b | _ => .skip
def insYes : ProgHOL 64 → ProgHOL 64 | .ite _ a _ => a | _ => .skip
def insNo : ProgHOL 64 → ProgHOL 64 | .ite _ _ b => b | _ => .skip
def insCont : ProgHOL 64 → ProgHOL 64 | .decCall _ _ _ _ b => b | _ => .skip

def insFnCode : ProgHOL 64 := sourceFnBody Guest.Software.guestFn__mpt_insert_node
def insLoopSeq : ProgHOL 64 := insDecBody (insDecBody (insDecBody insFnCode))
def insBody : ProgHOL 64 := insWhileBody (insLeft insLoopSeq)
def insCore : ProgHOL 64 := insDecBody (insDecBody (insDecBody (insDecBody insBody)))
def insSelect : ProgHOL 64 := insLeft (insRight insCore)
def insNonnull : ProgHOL 64 := insNo insSelect
def insKinds : ProgHOL 64 := insRight (insRight (insDecBody insNonnull))
def insExt : ProgHOL 64 := insYes (insNo insKinds)
def insExtDecision : ProgHOL 64 := insCont (insDecBody (insDecBody insExt))
def insExtDescend : ProgHOL 64 := insYes insExtDecision
def insExtSplit : ProgHOL 64 := insNo insExtDecision
def insBranch : ProgHOL 64 := insNo (insNo insKinds)

theorem insFn_eq : insFnCode =
    .dec (ofString "result") .one (.const 0)
      (.dec (ofString "slot") .one (.const 0)
        (.dec (ofString "go") .one (.const 1)
          (.seq
            (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody)
            (.return (.var .local (ofString "result")))))) := rfl

theorem insBody_eq : insBody =
    .dec (ofString "r") .one (.const 0)
      (.dec (ofString "next_node") .one (.const 0)
        (.dec (ofString "next_slot") .one (.const 0)
          (.dec (ofString "next_level") .one (.const 0)
            (.seq (.assign .local (ofString "go") (.const 0))
              (.seq insSelect insFinishProg))))) := rfl

theorem insSelect_eq : insSelect =
    .ite (.cmp .equal (.var .local (ofString "node")) (.const 0))
      (.call (some (some (.local, ofString "r"), none)) (ofString "node_new_leaf")
        [.op .add [.var .local (ofString "key"), .var .local (ofString "level")],
         .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")],
         .var .local (ofString "vptr"),
         .var .local (ofString "vlen")])
      insNonnull := by
  dsimp only [insSelect, insNonnull, insNo, insLeft, insRight, insCore, insDecBody, insBody,
    insWhileBody, insLoopSeq, insFnCode, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__mpt_insert_node,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural]
  rfl

theorem insNonnull_eq : insNonnull =
    .dec (ofString "k") .one (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 2])
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
          insKinds)) := rfl

theorem insKinds_eq : insKinds =
    .ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
      (.call (some (some (.local, ofString "r"), none)) (ofString "_insert_into_leaf")
        [.var .local (ofString "node"),
         .op .add [.var .local (ofString "key"), .var .local (ofString "level")],
         .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")],
         .var .local (ofString "vptr"),
         .var .local (ofString "vlen")])
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 2))
        insExt
        insBranch) := rfl

theorem insExt_eq : insExt =
    .dec (ofString "seg") .one (.load .one (.op .add [.var .local (ofString "node"), .const 32]))
      (.dec (ofString "sl") .one (.load .one (.op .add [.var .local (ofString "node"), .const 40]))
        (.decCall (ofString "pl") .one (ofString "common_prefix_length")
          [.var .local (ofString "seg"),
           .var .local (ofString "sl"),
           .op .add [.var .local (ofString "key"), .var .local (ofString "level")],
           .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")]]
          insExtDecision)) := rfl

theorem insExtDecision_eq : insExtDecision =
    .ite (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl")))
      insExtDescend
      insExtSplit := rfl

theorem insExtDescend_eq : insExtDescend =
    .seq (.assign .local (ofString "r") (.var .local (ofString "node")))
      (.seq (.assign .local (ofString "next_node")
          (.load .one (.op .add [.var .local (ofString "node"), .const 48])))
        (.seq (.assign .local (ofString "next_slot")
            (.op .add [.var .local (ofString "node"), .const 48]))
          (.seq (.assign .local (ofString "next_level")
              (.op .add [.var .local (ofString "level"), .var .local (ofString "pl")]))
            (.assign .local (ofString "go") (.const 1))))) := rfl

theorem insExtSplit_eq : insExtSplit =
    .decCall (ofString "br") .one (ofString "_split_extension")
      [.var .local (ofString "node"),
       .op .add [.var .local (ofString "key"), .var .local (ofString "level")],
       .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")],
       .var .local (ofString "vptr"),
       .var .local (ofString "vlen"),
       .var .local (ofString "pl")]
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "pl")))
        (.call (some (some (.local, ofString "r"), none)) (ofString "node_new_ext")
          [.var .local (ofString "seg"), .var .local (ofString "pl"), .var .local (ofString "br")])
        (.assign .local (ofString "r") (.var .local (ofString "br")))) := rfl

theorem insBranch_eq : insBranch =
    .ite (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 160]) (.var .local (ofString "vptr")))
        (.seq (.store (.op .add [.var .local (ofString "node"), .const 168]) (.var .local (ofString "vlen")))
          (.assign .local (ofString "r") (.var .local (ofString "node")))))
      (.dec (ofString "idx") .one
        (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]))
        (.seq (.assign .local (ofString "r") (.var .local (ofString "node")))
          (.seq (.assign .local (ofString "next_node")
              (.load .one (.op .add [.var .local (ofString "node"), .const 32,
                .panop .mul [.var .local (ofString "idx"), .const 8]])))
            (.seq (.assign .local (ofString "next_slot")
                (.op .add [.var .local (ofString "node"), .const 32,
                  .panop .mul [.var .local (ofString "idx"), .const 8]]))
              (.seq (.assign .local (ofString "next_level")
                  (.op .add [.var .local (ofString "level"), .const 1]))
                (.assign .local (ofString "go") (.const 1))))))) := rfl

theorem seq_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.seq a b) = (none, t)) :
    ∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧ evaluateHOLFiniteState mid b = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases h1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  rw [h1] at h
  cases r1 with
  | none => exact ⟨mid, rfl, h⟩
  | some _ => simp at h

theorem dec_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec x sh e b) = (none, t)) :
    ∃ v u,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      evaluateHOLFiniteState (setVarHOLFinite x v s) b = (none, u) ∧
      t = { u with locals := HolFiniteMapExact.resVarEq u.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · rw [he] at h; simp at h
  · rw [he] at h; dsimp only at h
    split at h
    · rcases hb : evaluateHOLFiniteState (setVarHOLFinite x v s) b with ⟨rb, u⟩
      have hb' : evaluateHOLFiniteState (setVarHOLFinite x v s) b = (rb, u) := hb
      rw [hb] at h
      cases rb with
      | none =>
        injection h with _ ht
        exact ⟨v, u, rfl, hb', ht.symm⟩
      | some _ => simp at h
    · simp at h

theorem call_assign_local_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (some (.local, x), none)) fname args) = (none, t)) :
    ∃ values body callee retShape rv post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      t = setVarHOLFinite x rv { post with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hl] at h; simp at h
    · have hl' : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) := hl
      rw [hl] at h; dsimp only at h
      split at h
      · simp at h
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        rw [hrun] at h
        rcases r with _ | r'
        · simp at h
        · cases r' with
          | returned rv =>
            dsimp only at h
            split at h
            · split at h
              · injection h with _ ht
                exact ⟨values, body, callee, retShape, rv, post, rfl, hl', hrun', ht.symm⟩
              · simp at h
            · simp at h
          | _ => simp at h

theorem call_void_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, t)) :
    ∃ values body callee retShape rv post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      t = { post with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hl] at h; simp at h
    · have hl' : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) := hl
      rw [hl] at h; dsimp only at h
      split at h
      · simp at h
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        rw [hrun] at h
        rcases r with _ | r'
        · simp at h
        · cases r' with
          | returned rv =>
            dsimp only at h
            split at h
            · injection h with _ ht
              exact ⟨values, body, callee, retShape, rv, post, rfl, hl', hrun', ht.symm⟩
            · simp at h
          | _ => simp at h

theorem decCall_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall x sh fname args cont) = (none, t)) :
    ∃ values body callee retShape rv post u,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont = (none, u) ∧
      t = { u with locals := HolFiniteMapExact.resVarEq u.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hl] at h; simp at h
    · have hl' : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) := hl
      rw [hl] at h; dsimp only at h
      split at h
      · simp at h
      · have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) = (r, post) := by
          rw [hrun] at hrem ⊢
          simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
        rw [hfix, hrun] at h; dsimp only at h
        rcases r with _ | r'
        · simp at h
        · cases r' with
          | returned rv =>
            dsimp only at h
            split at h
            · rcases hcont : evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont with ⟨rc, u⟩
              have hcont' : evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont = (rc, u) := hcont
              rw [hcont] at h
              cases rc with
              | none =>
                injection h with _ ht
                exact ⟨values, body, callee, retShape, rv, post, u, rfl, hl', hrun', hcont', ht.symm⟩
              | some _ => simp at h
            · simp at h
          | _ => simp at h


/-! ## 5. Selection & Body Step Proof for `_mpt_insert_node` -/

/-- Helper: `(wkey + wlevel).toNat = wkey.toNat + wlevel.toNat` when `KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat)`
with `wklen.toNat - wlevel.toNat ≠ 0`, and either way `KeyIn s Nd (wkey + wlevel).toNat (wklen - wlevel).toNat`. -/
theorem keyIn_suffix_bv {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {wkey wklen wlevel : BitVec 64}
    (hle : wlevel.toNat ≤ wklen.toNat)
    (hkey : KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat)) :
    (wklen - wlevel).toNat = wklen.toNat - wlevel.toNat ∧
    KeyIn s Nd (wkey + wlevel).toNat (wklen - wlevel).toNat := by
  have hsub : (wklen - wlevel).toNat = wklen.toNat - wlevel.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)
  refine ⟨hsub, ?_⟩
  rw [hsub]
  by_cases hz : wklen.toNat - wlevel.toNat = 0
  · exact Or.inl hz
  · obtain ⟨hnib, hal, hins, hd⟩ := hkey.resolve_left hz
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hfit : wkey.toNat + wlevel.toNat < 2 ^ 64 := by dsimp [Inside] at hins; omega
    have hadd : (wkey + wlevel).toNat = wkey.toNat + wlevel.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
    rw [hadd]
    exact Or.inr ⟨hnib, hal, hins, hd⟩

/-- Load aligned word `k` (`k < nodeSize (memW s wnode.toNat)`, `k % 8 = 0`) from `wnode ∈ Nd`. -/
theorem eval_load_node_field {F : Type} {st : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {wnode : BitVec 64}
    (hNd : NodeHeap st Nd) (hn : wnode.toNat ∈ Nd)
    (hlk : st.locals.lookup (ofString "node") = some (.val (.word wnode)))
    (k : Nat) (hk : k < nodeSize (memW st wnode.toNat)) (hk8 : k % 8 = 0) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 k)])) =
      some (.val (.word (BitVec.ofNat 64 (memW st (wnode.toNat + k))))) ∧
    (BitVec.ofNat 64 (memW st (wnode.toNat + k))).toNat = memW st (wnode.toNat + k) := by
  have hp := hNd.1 wnode.toNat hn
  have hins := hp.2.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  obtain ⟨_, _, hsz8⟩ := nodeSize_bounds (memW st wnode.toNat)
  obtain ⟨w_at, hdom_at, hm_at⟩ := hp.2.2.2.1.2.2 (k / 8) (by dsimp [nodeIvl]; omega)
  dsimp [nodeIvl] at hdom_at hm_at
  have hmul : wnode.toNat + 8 * (k / 8) = wnode.toNat + k := by omega
  rw [hmul] at hdom_at hm_at
  have hlt : wnode.toNat + k < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
  have hadd : wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hmw_eq : BitVec.ofNat 64 (memW st (wnode.toNat + k)) = w_at := by
    unfold memW; rw [hm_at]; simp
  refine ⟨?_, ?_⟩
  · simp [evalHOLExact, evalListHOLExact, hlk, valueIsWord, valueWord, wordOpHOL, wordOp,
      isWfShapeExactHOL, memLoadHOLExact, hadd, hdom_at, hm_at, hmw_eq]
  · rw [hmw_eq]; unfold memW; rw [hm_at]

/-- Selection postcondition before `insFinishProg`. -/
def InsSelectPost {F : Type} (s0 u : PanSemStateFiniteExact 64 F) (Nd0 : List Nat)
    (wkey wklen wvptr wvlen wslot wres : BitVec 64) : Prop :=
  ∃ (Nd' : List Nat) (wr wnn wns wnl wgo : BitVec 64),
    NodeStep s0 u Nd0 Nd' ∧
    u.code = originalRuntimeCode ∧
    u.locals.lookup (ofString "key") = some (.val (.word wkey)) ∧
    u.locals.lookup (ofString "klen") = some (.val (.word wklen)) ∧
    u.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) ∧
    u.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) ∧
    u.locals.lookup (ofString "slot") = some (.val (.word wslot)) ∧
    u.locals.lookup (ofString "result") = some (.val (.word wres)) ∧
    u.locals.lookup (ofString "r") = some (.val (.word wr)) ∧
    u.locals.lookup (ofString "next_node") = some (.val (.word wnn)) ∧
    u.locals.lookup (ofString "next_slot") = some (.val (.word wns)) ∧
    u.locals.lookup (ofString "next_level") = some (.val (.word wnl)) ∧
    u.locals.lookup (ofString "go") = some (.val (.word wgo)) ∧
    RootIn Nd' wr.toNat ∧
    (wslot = 0 ∨ (ValidSlot u Nd' wslot.toNat ∧ wres.toNat ∈ Nd')) ∧
    (wgo ≠ 0 →
      wnl.toNat ≤ wklen.toNat ∧
      RootIn Nd' wnn.toNat ∧
      KeyIn u Nd' (wkey.toNat + wnl.toNat) (wklen.toNat - wnl.toNat) ∧
      ValidSlot u Nd' wns.toNat ∧
      wns ≠ 0 ∧
      wr.toNat ∈ Nd')

theorem InsSelectPost.restore_local {F : Type}
    {s0 u : PanSemStateFiniteExact 64 F} {Nd0 : List Nat}
    {wkey wklen wvptr wvlen wslot wres : BitVec 64}
    {x : String} {old : Option (ValueHOL 64)}
    (h : InsSelectPost s0 u Nd0 wkey wklen wvptr wvlen wslot wres)
    (hne : ∀ m ∈ ["key", "klen", "vptr", "vlen", "slot", "result", "r", "next_node", "next_slot", "next_level", "go"],
      ofString m ≠ ofString x) :
    InsSelectPost s0 { u with locals := HolFiniteMapExact.resVarEq u.locals (ofString x, old) }
      Nd0 wkey wklen wvptr wvlen wslot wres := by
  obtain ⟨Nd', wr, wnn, wns, wnl, wgo, hst, huc, hk, hkl, hvp, hvl, hsl, hrs, hr, hnn, hns, hnl, hgo,
    hroot, hsl_inv, hnxt⟩ := h
  have hlk (m : String)
      (hm : m ∈ ["key", "klen", "vptr", "vlen", "slot", "result", "r", "next_node", "next_slot", "next_level", "go"]) :
      (HolFiniteMapExact.resVarEq u.locals (ofString x, old)).lookup (ofString m) =
        u.locals.lookup (ofString m) :=
    resVarEq_lookup_ne u.locals (ofString x) (ofString m) old (hne m hm)
  exact ⟨Nd', wr, wnn, wns, wnl, wgo,
    hst.with_locals_clock _ u.clock, huc,
    (hlk "key" (by simp)).trans hk,
    (hlk "klen" (by simp)).trans hkl,
    (hlk "vptr" (by simp)).trans hvp,
    (hlk "vlen" (by simp)).trans hvl,
    (hlk "slot" (by simp)).trans hsl,
    (hlk "result" (by simp)).trans hrs,
    (hlk "r" (by simp)).trans hr,
    (hlk "next_node" (by simp)).trans hnn,
    (hlk "next_slot" (by simp)).trans hns,
    (hlk "next_level" (by simp)).trans hnl,
    (hlk "go" (by simp)).trans hgo,
    hroot, hsl_inv, hnxt⟩

/-- Local assignment inversion for word expression. -/
theorem assign_local_eval_inv {F : Type} {st st' : PanSemStateFiniteExact 64 F}
    {x : String} {e : ExpHOL 64} {w : BitVec 64}
    (hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e =
      some (.val (.word w)))
    (hass : evaluateHOLFiniteState st (.assign .local (ofString x) e) = (none, st')) :
    st' = setVarHOLFinite (ofString x) (.val (.word w)) st := by
  rw [evaluateHOLFiniteState_assign, hev] at hass
  dsimp only at hass
  split at hass
  · injection hass with _ heq; exact heq.symm
  · simp at hass

/-- Extension case (`k == 2`) after `node_invalidate`: proves `InsSelectPost`. -/
theorem insExt_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Nd0 Nd : List Nat}
    {wkey wklen wvptr wvlen wnode wslot wlevel wres : BitVec 64}
    {u : PanSemStateFiniteExact 64 F}
    (ha0 : ArenaReady s0)
    (hstep : NodeStep s0 s Nd0 Nd)
    (hsc : s.code = originalRuntimeCode)
    (hnode_in : wnode.toNat ∈ Nd)
    (hnode_k2 : memW s wnode.toNat = 2)
    (hle : wlevel.toNat ≤ wklen.toNat)
    (hvlt : wvlen.toNat < 2 ^ 40)
    (hklt : wklen.toNat ≤ 64)
    (hkey : KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat))
    (hsl_inv : wslot = 0 ∨ (ValidSlot s Nd wslot.toNat ∧ wres.toNat ∈ Nd))
    (hs_key : s.locals.lookup (ofString "key") = some (.val (.word wkey)))
    (hs_klen : s.locals.lookup (ofString "klen") = some (.val (.word wklen)))
    (hs_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word wvptr)))
    (hs_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word wvlen)))
    (hs_node : s.locals.lookup (ofString "node") = some (.val (.word wnode)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word wslot)))
    (hs_level : s.locals.lookup (ofString "level") = some (.val (.word wlevel)))
    (hs_res : s.locals.lookup (ofString "result") = some (.val (.word wres)))
    (hs_nn : s.locals.lookup (ofString "next_node") = some (.val (.word 0)))
    (hs_ns : s.locals.lookup (ofString "next_slot") = some (.val (.word 0)))
    (hs_nl : s.locals.lookup (ofString "next_level") = some (.val (.word 0)))
    (hs_go : s.locals.lookup (ofString "go") = some (.val (.word 0)))
    (hrun : evaluateHOLFiniteState s insExt = (none, u)) :
    InsSelectPost s0 u Nd0 wkey wklen wvptr wvlen wslot wres := by
  rw [insExt_eq] at hrun
  have hsz2 : nodeSize (memW s wnode.toNat) = 56 := by simp [nodeSize, hnode_k2]
  obtain ⟨hev_seg, hwseg_nat⟩ := eval_load_node_field hstep.heap hnode_in hs_node 32 (by omega) (by decide)
  obtain ⟨vseg, u_seg, hev1, hrun1, hu_eq⟩ := dec_none_inv hrun
  change _ = some _ at hev_seg
  have hvseg : vseg = .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 32)))) :=
    Option.some.inj (hev1.symm.trans hev_seg)
  subst hvseg
  set wseg := BitVec.ofNat 64 (memW s (wnode.toNat + 32))
  set s1 := setVarHOLFinite (ofString "seg") (.val (.word wseg)) s
  have hs1_node : s1.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_node,
      show ofString "seg" ≠ ofString "node" by decide]
  obtain ⟨hev_sl, hwsl_nat⟩ := eval_load_node_field (st := s1) hstep.heap hnode_in hs1_node 40
    (by change 40 < nodeSize (memW s wnode.toNat); omega) (by decide)
  obtain ⟨vsl, u_sl, hev2, hrun2, huseg_eq⟩ := dec_none_inv hrun1
  have hvsl : vsl = .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 40)))) :=
    Option.some.inj (hev2.symm.trans hev_sl)
  subst hvsl
  set wsl := BitVec.ofNat 64 (memW s (wnode.toNat + 40))
  have hwsl_s_nat : wsl.toNat = memW s (wnode.toNat + 40) := hwsl_nat
  set s2 := setVarHOLFinite (ofString "sl") (.val (.word wsl)) s1
  -- Now invert `decCall pl := common_prefix_length(seg, sl, key + level, klen - level) insExtDecision` on `s2`
  obtain ⟨cvals, cbody, ccallee, cret, crv, cpost, u_pl, hcargs, hcl, hcrun, hrun3, husl_eq⟩ :=
    decCall_none_inv hrun2
  have hs2_other : ∀ x : MlS, x ≠ ofString "sl" → x ≠ ofString "seg" → s2.locals.lookup x = s.locals.lookup x := by
    intro x h1 h2
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, Ne.symm h2]
  have hs2_seg : s2.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sl" ≠ ofString "seg" by decide]
  have hs2_sl : s2.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_key : s2.locals.lookup (ofString "key") = some (.val (.word wkey)) :=
    (hs2_other _ (by decide) (by decide)).trans hs_key
  have hs2_level : s2.locals.lookup (ofString "level") = some (.val (.word wlevel)) :=
    (hs2_other _ (by decide) (by decide)).trans hs_level
  have hs2_klen : s2.locals.lookup (ofString "klen") = some (.val (.word wklen)) :=
    (hs2_other _ (by decide) (by decide)).trans hs_klen
  have hcvals_eq : cvals = [.val (.word wseg), .val (.word wsl), .val (.word (wkey + wlevel)), .val (.word (wklen - wlevel))] := by
    rw [evalListHOLFinite_eq_toExact] at hcargs
    simpa [evalListHOLExact, evalHOLExact, hs2_seg, hs2_sl, hs2_key, hs2_level, hs2_klen,
      valueIsWord, valueWord, wordOpHOL, wordOp] using hcargs.symm
  subst hcvals_eq
  have hs2_code : s2.code = originalRuntimeCode := hsc
  have hcl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "common_prefix_length")
      [.val (.word wseg), .val (.word wsl), .val (.word (wkey + wlevel)), .val (.word (wklen - wlevel))] =
      some (cbody, ccallee, cret) := by rwa [← hs2_code]
  obtain ⟨_, hcp_al⟩ := lookup_param_exact lookup_common_prefix_length hcl_code
    [(ofString "a", .one)] "al" .one [(ofString "b", .one), (ofString "bl", .one)]
    [.val (.word wseg)] (.val (.word wsl)) [.val (.word (wkey + wlevel)), .val (.word (wklen - wlevel))]
    rfl rfl rfl (by decide)
  obtain ⟨_, hcp_bl⟩ := lookup_param_exact lookup_common_prefix_length hcl_code
    [(ofString "a", .one), (ofString "al", .one), (ofString "b", .one)] "bl" .one []
    [.val (.word wseg), .val (.word wsl), .val (.word (wkey + wlevel))] (.val (.word (wklen - wlevel))) []
    rfl rfl rfl (by decide)
  have hs2_G : GuestInv s2 := guestInv_with_locals_clock s _ _ hstep.arena.1
  have hro_cpl := FunSpec.at_lookup ro_common_prefix_length_spec s2 hs2_code
    _ cbody ccallee cret hcl (guestInv_callEntry s2 ccallee hs2_G)
    (by rw [hcrun]; simp) (by rw [hcrun]; exact Or.inl ⟨crv, rfl⟩)
  have hrv_spec : RetLe (fun st => min (locN st "al") (locN st "bl")) (ofString "common_prefix_length") := by
    rcases Wave8Contracts.M27.rv_common_prefix_length with ⟨ps, bd, rt, hlk_rv, hrun_rv⟩
    exact ⟨ps, bd, rt, hlk_rv, fun st hc hg hex hnt => hrun_rv st hc hg hex hnt⟩
  have hrv_cpl := FunSpec.at_lookup hrv_spec s2 hs2_code
    _ cbody ccallee cret hcl (guestInv_callEntry s2 ccallee hs2_G)
    (by rw [hcrun]; simp) crv (by rw [hcrun])
  rw [hcrun] at hro_cpl; dsimp only at hro_cpl
  obtain ⟨wpl, rfl, hwpl_le⟩ := hrv_cpl
  dsimp only at hwpl_le
  obtain ⟨hk_sub_nat, hkey_bv⟩ := keyIn_suffix_bv hle hkey
  have hal_ent : locN (callEntryStateHOLFinite s2 ccallee) "al" = wsl.toNat := by
    simp [locN, callEntryStateHOLFinite, hcp_al]
  have hbl_ent : locN (callEntryStateHOLFinite s2 ccallee) "bl" = wklen.toNat - wlevel.toNat := by
    simp [locN, callEntryStateHOLFinite, hcp_bl, hk_sub_nat]
  rw [hal_ent, hbl_ent] at hwpl_le
  have hwpl_sl : wpl.toNat ≤ wsl.toNat := Nat.le_trans hwpl_le (Nat.min_le_left _ _)
  have hwpl_rem : wpl.toNat ≤ wklen.toNat - wlevel.toNat := Nat.le_trans hwpl_le (Nat.min_le_right _ _)
  set s3 := setVarHOLFinite (ofString "pl") (.val (.word wpl)) { cpost with locals := s2.locals }
  have hs3_frame : s3 = { s with locals := s3.locals, clock := s3.clock } := by
    dsimp only [s3, setVarHOLFinite]; rw [hro_cpl]; rfl
  have hstep3 : NodeStep s0 s3 Nd0 Nd := by
    have : NodeStep s0 { s with locals := s3.locals, clock := s3.clock } Nd0 Nd :=
      hstep.with_locals_clock s3.locals s3.clock
    rwa [← hs3_frame] at this
  have hs3_other : ∀ x : MlS, x ≠ ofString "pl" → x ≠ ofString "sl" → x ≠ ofString "seg" →
      s3.locals.lookup x = s.locals.lookup x := by
    intro x h1 h2 h3
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, hs2_other x h2 h3]
  have hs3_pl : s3.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_sl : s3.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sl,
      show ofString "pl" ≠ ofString "sl" by decide]
  have hs3_seg : s3.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_seg,
      show ofString "pl" ≠ ofString "seg" by decide]
  -- Suffix wrapper restoring `pl`, `sl`, `seg`
  suffices hdec3 : InsSelectPost s0 u_pl Nd0 wkey wklen wvptr wvlen wslot wres by
    rw [hu_eq, huseg_eq, husl_eq]
    exact ((hdec3.restore_local (by decide)).restore_local (by decide)).restore_local (by decide)
  -- Evaluate `insExtDecision` on `s3`
  rw [insExtDecision_eq, evaluateHOLFiniteState_ite] at hrun3
  have hc_pl_sl : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl"))) =
      some (.val (.word (if wpl = wsl then 1 else 0))) := by
    simp [evalHOLExact, hs3_pl, hs3_sl, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc_pl_sl] at hrun3
  by_cases hpl_eq : wpl = wsl
  · -- Descent arm (`pl == sl`): `r = node; next_node = load(node + 48); next_slot = node + 48; next_level = level + pl; go = 1`
    rw [if_pos hpl_eq] at hrun3
    simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hrun3
    rw [insExtDescend_eq] at hrun3
    have hs3_node : s3.locals.lookup (ofString "node") = some (.val (.word wnode)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_node
    have hs3_level : s3.locals.lookup (ofString "level") = some (.val (.word wlevel)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_level
    obtain ⟨d1, hd1, hr1⟩ := seq_none_inv hrun3
    have hd1_eq := assign_local_eval_inv (w := wnode) (by exact hs3_node) hd1
    subst hd1_eq
    set d1 := setVarHOLFinite (ofString "r") (.val (.word wnode)) s3
    have hd1_node : d1.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_node,
        show ofString "r" ≠ ofString "node" by decide]
    have hmw_s3 : ∀ a, memW d1 a = memW s a := fun a => by
      have hm_eq : d1.memory = s.memory := by
        change s3.memory = s.memory
        rw [hs3_frame]
      unfold memW; rw [hm_eq]
    obtain ⟨hev_ch, hwch_nat⟩ := eval_load_node_field (st := d1) hstep3.heap hnode_in hd1_node 48
      (by rw [hmw_s3, hsz2]; decide) (by decide)
    obtain ⟨d2, hd2, hr2⟩ := seq_none_inv hr1
    have hd2_eq := assign_local_eval_inv hev_ch hd2
    subst hd2_eq
    set wch := BitVec.ofNat 64 (memW d1 (wnode.toNat + 48))
    set d2 := setVarHOLFinite (ofString "next_node") (.val (.word wch)) d1
    have hd2_node : d2.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_node,
        show ofString "next_node" ≠ ofString "node" by decide, show ofString "r" ≠ ofString "node" by decide]
    obtain ⟨d3, hd3, hr3⟩ := seq_none_inv hr2
    have hev_ns : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
        (.op .add [.var .local (ofString "node"), .const 48]) =
        some (.val (.word (wnode + 48))) := by
      simp [evalHOLExact, evalListHOLExact, hd2_node, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hd3_eq := assign_local_eval_inv hev_ns hd3
    subst hd3_eq
    set d3 := setVarHOLFinite (ofString "next_slot") (.val (.word (wnode + 48))) d2
    have hd3_level : d3.locals.lookup (ofString "level") = some (.val (.word wlevel)) := by
      simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_level,
        show ofString "next_slot" ≠ ofString "level" by decide,
        show ofString "next_node" ≠ ofString "level" by decide,
        show ofString "r" ≠ ofString "level" by decide]
    have hd3_pl : d3.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_pl,
        show ofString "next_slot" ≠ ofString "pl" by decide,
        show ofString "next_node" ≠ ofString "pl" by decide,
        show ofString "r" ≠ ofString "pl" by decide]
    obtain ⟨d4, hd4, hr4⟩ := seq_none_inv hr3
    have hev_nl : @evalHOLExact 64 F _ d3.toExact (fun a => Classical.propDecidable (d3.memaddrs a))
        (.op .add [.var .local (ofString "level"), .var .local (ofString "pl")]) =
        some (.val (.word (wlevel + wpl))) := by
      simp [evalHOLExact, evalListHOLExact, hd3_level, hd3_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hd4_eq := assign_local_eval_inv hev_nl hd4
    subst hd4_eq
    set d4 := setVarHOLFinite (ofString "next_level") (.val (.word (wlevel + wpl))) d3
    have hd5_eq := assign_local_eval_inv (w := 1) rfl hr4
    subst hd5_eq
    set df := setVarHOLFinite (ofString "go") (.val (.word 1)) d4
    have hdf_other : ∀ x : MlS,
        x ≠ ofString "go" → x ≠ ofString "next_level" → x ≠ ofString "next_slot" →
        x ≠ ofString "next_node" → x ≠ ofString "r" →
        df.locals.lookup x = s3.locals.lookup x := by
      intro x h1 h2 h3 h4 h5
      simp [df, d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
    have hstep_df : NodeStep s0 df Nd0 Nd := hstep3.with_locals_clock df.locals df.clock
    have hdf_code : df.code = originalRuntimeCode := by rw [show df.code = s3.code from rfl, hs3_frame]; exact hsc
    have hstep_s_df : NodeStep s df Nd Nd := by
      have hdf_eq : df = { s with locals := df.locals, clock := df.clock } := by
        have hs3_eq := hs3_frame
        dsimp only [df, d4, d3, d2, d1, setVarHOLFinite]
        conv_lhs => rw [hs3_eq]
      rw [hdf_eq]
      exact (NodeStep.refl hstep.arena hstep.heap).with_locals_clock df.locals df.clock
    have hdf_mem_s : df.memory = s.memory := by
      change s3.memory = s.memory; rw [hs3_frame]
    have hdf_mw_s : ∀ a, memW df a = memW s a := fun a => by unfold memW; rw [hdf_mem_s]
    refine ⟨Nd, wnode, wch, wnode + 48, wlevel + wpl, 1,
      hstep_df, hdf_code,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_key),
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_klen),
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_vptr),
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_vlen),
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_slot),
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hs3_other _ (by decide) (by decide) (by decide)).trans hs_res),
      by simp [df, d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "r" by decide,
           show ofString "next_level" ≠ ofString "r" by decide,
           show ofString "next_slot" ≠ ofString "r" by decide,
           show ofString "next_node" ≠ ofString "r" by decide],
      by simp [df, d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_node" by decide,
           show ofString "next_level" ≠ ofString "next_node" by decide,
           show ofString "next_slot" ≠ ofString "next_node" by decide],
      by simp [df, d4, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_slot" by decide,
           show ofString "next_level" ≠ ofString "next_slot" by decide],
      by simp [df, d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_level" by decide],
      by simp [df, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      Or.inr hnode_in,
      hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_df, hrin⟩),
      ?_⟩
    intro _
    have hnl_nat : (wlevel + wpl).toNat = wlevel.toNat + wpl.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hns_nat : (wnode + (48 : BitVec 64)).toNat = wnode.toNat + 48 := by
      have hins := (hstep.heap.1 wnode.toNat hnode_in).2.2.1
      have hhl_lt : heapLimit < 2 ^ 64 := by decide
      dsimp [Inside, nodeIvl] at hins
      have h48 : (48 : BitVec 64).toNat = 48 := by decide
      rw [BitVec.toNat_add, h48, Nat.mod_eq_of_lt (by omega)]
    have hns_nz : wnode + (48 : BitVec 64) ≠ 0 := by
      intro hz; have := congrArg BitVec.toNat hz
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [hns_nat, h0] at this; omega
    have hwch_root : RootIn Nd wch.toNat := by
      rw [hwch_nat, hmw_s3]
      exact (hstep.heap.1 wnode.toNat hnode_in).2.2.2.2.1 hnode_k2
    have hkey_df : KeyIn df Nd (wkey.toNat + (wlevel + wpl).toNat) (wklen.toNat - (wlevel + wpl).toNat) := by
      rw [hnl_nat]
      by_cases hrem0 : wklen.toNat - (wlevel.toNat + wpl.toNat) = 0
      · exact Or.inl hrem0
      · have hlen_nz : wklen.toNat - wlevel.toNat ≠ 0 := by omega
        obtain ⟨hnib, hal, hins, hd⟩ := hkey.resolve_left hlen_nz
        have hhl_lt : heapLimit < 2 ^ 64 := by decide
        have hsub_s : KeyIn s Nd ((BitVec.ofNat 64 (wkey.toNat + wlevel.toNat) + BitVec.ofNat 64 wpl.toNat).toNat)
            (wklen.toNat - (wlevel.toNat + wpl.toNat)) :=
          keyIn_subslice hkey (by omega)
        have hpo : (BitVec.ofNat 64 (wkey.toNat + wlevel.toNat) + BitVec.ofNat 64 wpl.toNat).toNat =
            wkey.toNat + (wlevel.toNat + wpl.toNat) := by
          dsimp [Inside] at hins
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        rw [hpo] at hsub_s
        exact hstep_s_df.keyIn hstep.arena hstep.heap hsub_s
    have hvslot_ns : ValidSlot df Nd (wnode + 48).toNat := by
      refine ⟨wnode.toNat, hnode_in, Or.inl ⟨?_, hns_nat⟩⟩
      rw [hdf_mw_s]
      exact hnode_k2
    exact ⟨by rw [hnl_nat]; omega, hwch_root, hkey_df, hvslot_ns, hns_nz, hnode_in⟩
  · -- Split arm (`pl != sl`): `pl < sl`, calls `_split_extension`, then `if 0 < pl` calls `node_new_ext` else `r = br`
    rw [if_neg hpl_eq] at hrun3
    simp only [↓reduceIte] at hrun3
    have hwpl_lt_sl : wpl.toNat < wsl.toNat := by
      apply Nat.lt_of_le_of_ne hwpl_sl
      intro heq; exact hpl_eq (BitVec.eq_of_toNat_eq heq)
    rw [insExtSplit_eq] at hrun3
    obtain ⟨spvals, spbody, spcallee, spret, sprv, sppost, u_br, hspargs, hspl, hsprun, hspcont, hubr_eq⟩ :=
      decCall_none_inv hrun3
    have hs3_node : s3.locals.lookup (ofString "node") = some (.val (.word wnode)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_node
    have hs3_key : s3.locals.lookup (ofString "key") = some (.val (.word wkey)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_key
    have hs3_level : s3.locals.lookup (ofString "level") = some (.val (.word wlevel)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_level
    have hs3_klen : s3.locals.lookup (ofString "klen") = some (.val (.word wklen)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_klen
    have hs3_vptr : s3.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_vptr
    have hs3_vlen : s3.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) :=
      (hs3_other _ (by decide) (by decide) (by decide)).trans hs_vlen
    have hspvals_eq : spvals = [.val (.word wnode), .val (.word (wkey + wlevel)), .val (.word (wklen - wlevel)),
        .val (.word wvptr), .val (.word wvlen), .val (.word wpl)] := by
      rw [evalListHOLFinite_eq_toExact] at hspargs
      simpa [evalListHOLExact, evalHOLExact, hs3_node, hs3_key, hs3_level, hs3_klen, hs3_vptr, hs3_vlen, hs3_pl,
        valueIsWord, valueWord, wordOpHOL, wordOp] using hspargs.symm
    subst hspvals_eq
    have hs3_code : s3.code = originalRuntimeCode := by rw [hs3_frame]; exact hsc
    have hspl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_split_extension")
        [.val (.word wnode), .val (.word (wkey + wlevel)), .val (.word (wklen - wlevel)),
         .val (.word wvptr), .val (.word wvlen), .val (.word wpl)] =
        some (spbody, spcallee, spret) := by rwa [← hs3_code]
    obtain ⟨_, hsp_nd⟩ := lookup_param_exact lookup__split_extension hspl_code
      [] "node" .one [(ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
      [] (.val (.word wnode)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hsp_rk⟩ := lookup_param_exact lookup__split_extension hspl_code
      [(ofString "node", .one)] "rk" .one [(ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
      [_] (.val (.word (wkey + wlevel))) _ rfl rfl rfl (by decide)
    obtain ⟨_, hsp_rl⟩ := lookup_param_exact lookup__split_extension hspl_code
      [(ofString "node", .one), (ofString "rk", .one)] "rl" .one [(ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
      [_, _] (.val (.word (wklen - wlevel))) _ rfl rfl rfl (by decide)
    obtain ⟨_, hsp_vl⟩ := lookup_param_exact lookup__split_extension hspl_code
      [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one)] "vlen" .one [(ofString "pl", .one)]
      [_, _, _, _] (.val (.word wvlen)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hsp_pl⟩ := lookup_param_exact lookup__split_extension hspl_code
      [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)] "pl" .one []
      [_, _, _, _, _] (.val (.word wpl)) [] rfl rfl rfl (by decide)
    have hkey_s3 : KeyIn s3 Nd (wkey + wlevel).toNat (wklen - wlevel).toNat := by
      rw [hs3_frame]; exact hkey_bv
    obtain ⟨Nd_sp, hstep_sp, hret_sp⟩ := nodeStep_of_nodeFn nf__split_extension s3 hs3_code
      hstep3.arena hstep3.heap hspl
      (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hsp_nd]; exact Or.inr hnode_in)
      (by
        have hln : locN (callEntryStateHOLFinite s3 spcallee) "node" = wnode.toNat := by
          simp [locN, callEntryStateHOLFinite, hsp_nd]
        have hlrk : locN (callEntryStateHOLFinite s3 spcallee) "rk" = (wkey + wlevel).toNat := by
          simp [locN, callEntryStateHOLFinite, hsp_rk]
        have hlrl : locN (callEntryStateHOLFinite s3 spcallee) "rl" = (wklen - wlevel).toNat := by
          simp [locN, callEntryStateHOLFinite, hsp_rl]
        have hlvl : locN (callEntryStateHOLFinite s3 spcallee) "vlen" = wvlen.toNat := by
          simp [locN, callEntryStateHOLFinite, hsp_vl]
        have hlpl : locN (callEntryStateHOLFinite s3 spcallee) "pl" = wpl.toNat := by
          simp [locN, callEntryStateHOLFinite, hsp_pl]
        have hm40 : memW (callEntryStateHOLFinite s3 spcallee) (wnode.toNat + 40) = wsl.toNat := by
          change memW s3 (wnode.toNat + 40) = wsl.toNat
          rw [hs3_frame]; exact hwsl_nat.symm
        refine ⟨⟨by rw [hln]; exact hnode_in, by rw [hln]; change memW s3 wnode.toNat = 2; rw [hs3_frame]; exact hnode_k2⟩,
          by rw [hlrk, hlrl]; exact hkey_s3,
          by rw [hlvl]; exact hvlt,
          by rw [hln, hm40, hlpl]; exact hwpl_lt_sl,
          by rw [hlpl, hlrl, hk_sub_nat]; exact hwpl_rem⟩)
      (by rw [hsprun]; exact Or.inl ⟨sprv, rfl⟩)
    rw [hsprun] at hstep_sp hret_sp; dsimp only at hstep_sp hret_sp
    obtain ⟨wbr, rfl, hwbr_root⟩ := hret_sp sprv rfl
    set s4 := setVarHOLFinite (ofString "br") (.val (.word wbr)) { sppost with locals := s3.locals }
    have hstep_s3_s4 : NodeStep s3 s4 Nd Nd_sp := hstep_sp.with_locals_clock _ _
    have hstep4 : NodeStep s0 s4 Nd0 Nd_sp := NodeStep.trans ha0 hstep3 hstep_s3_s4
    have hs4_code : s4.code = originalRuntimeCode :=
      (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s3 spcallee) spbody).1.trans hs3_code |> fun h => by
        rw [hsprun] at h; exact h
    have hs4_br : s4.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs4_pl : s4.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_pl,
        show ofString "br" ≠ ofString "pl" by decide]
    have hs4_seg : s4.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_seg,
        show ofString "br" ≠ ofString "seg" by decide]
    have hs4_other : ∀ x : MlS, x ≠ ofString "br" → x ≠ ofString "pl" → x ≠ ofString "sl" → x ≠ ofString "seg" →
        s4.locals.lookup x = s.locals.lookup x := by
      intro x h1 h2 h3 h4
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, hs3_other x h2 h3 h4]
    have hsl_inv4 : wslot = 0 ∨ (ValidSlot s4 Nd_sp wslot.toNat ∧ wres.toNat ∈ Nd_sp) := by
      rcases hsl_inv with h0 | ⟨hv, hrin⟩
      · exact Or.inl h0
      · have hv3 : ValidSlot s3 Nd wslot.toNat := by rw [hs3_frame]; exact hv
        exact Or.inr ⟨hv3.mono hstep_s3_s4, hstep_s3_s4.sub _ hrin⟩
    suffices hbr_post : InsSelectPost s0 u_br Nd0 wkey wklen wvptr wvlen wslot wres by
      rw [hubr_eq]
      exact hbr_post.restore_local (by decide)
    -- Now evaluate `if 0 < pl { r = node_new_ext(seg, pl, br) } else { r = br }` on `s4`
    rw [evaluateHOLFiniteState_ite] at hspcont
    have hc_pl0 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.cmp .lower (.const 0) (.var .local (ofString "pl"))) =
        some (.val (.word (if (0 : BitVec 64) < wpl then 1 else 0))) := by
      simp [evalHOLExact, hs4_pl, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc_pl0] at hspcont
    by_cases hpl_pos : (0 : BitVec 64) < wpl
    · rw [if_pos hpl_pos] at hspcont
      simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hspcont
      obtain ⟨evals, ebody, ecallee, eret, erv, epost, heargs, hel, herun, hubr_set⟩ :=
        call_assign_local_none_inv hspcont
      have hevals_eq : evals = [.val (.word wseg), .val (.word wpl), .val (.word wbr)] := by
        rw [evalListHOLFinite_eq_toExact] at heargs
        simpa [evalListHOLExact, evalHOLExact, hs4_seg, hs4_pl, hs4_br] using heargs.symm
      subst hevals_eq
      have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
          [.val (.word wseg), .val (.word wpl), .val (.word wbr)] =
          some (ebody, ecallee, eret) := by rwa [← hs4_code]
      obtain ⟨_, hep_nib⟩ := lookup_param_exact lookup_node_new_ext hel_code
        [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
        [] (.val (.word wseg)) _ rfl rfl rfl (by decide)
      obtain ⟨_, hep_nlen⟩ := lookup_param_exact lookup_node_new_ext hel_code
        [(ofString "nib", .one)] "nlen" .one [(ofString "child", .one)]
        [_] (.val (.word wpl)) _ rfl rfl rfl (by decide)
      obtain ⟨_, hep_ch⟩ := lookup_param_exact lookup_node_new_ext hel_code
        [(ofString "nib", .one), (ofString "nlen", .one)] "child" .one []
        [_, _] (.val (.word wbr)) [] rfl rfl rfl (by decide)
      have hkey_seg_s : KeyIn s Nd wseg.toNat wsl.toNat := by
        rw [hwseg_nat, hwsl_s_nat]
        exact (hstep.heap.1 wnode.toNat hnode_in).2.2.2.2.2.2.1 (Or.inr hnode_k2)
      have hkey_seg_pl_s : KeyIn s Nd wseg.toNat wpl.toNat := by
        have h0 : (BitVec.ofNat 64 wseg.toNat + BitVec.ofNat 64 0).toNat = wseg.toNat := by simp
        rw [← h0]
        exact keyIn_subslice hkey_seg_s (by omega)
      have hkey_seg_pl_s4 : KeyIn s4 Nd_sp wseg.toNat wpl.toNat := by
        have hs3_k : KeyIn s3 Nd wseg.toNat wpl.toNat := by rw [hs3_frame]; exact hkey_seg_pl_s
        exact hstep_s3_s4.keyIn hstep3.arena hstep3.heap hs3_k
      obtain ⟨Nd_ext, hstep_ext, hret_ext⟩ := nodeStep_of_nodeFn nf_node_new_ext s4 hs4_code
        hstep4.arena hstep4.heap hel
        (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hep_ch]; exact hwbr_root)
        (by simp [locN, callEntryStateHOLFinite, hep_nib, hep_nlen]; exact hkey_seg_pl_s4)
        (by rw [herun]; exact Or.inl ⟨erv, rfl⟩)
      rw [herun] at hstep_ext hret_ext; dsimp only at hstep_ext hret_ext
      obtain ⟨wext, rfl, hwext_root⟩ := hret_ext erv rfl
      subst hubr_set
      set se := setVarHOLFinite (ofString "r") (.val (.word wext)) { epost with locals := s4.locals }
      have hstep_s4_se : NodeStep s4 se Nd_sp Nd_ext := hstep_ext.with_locals_clock _ _
      have hstep_se : NodeStep s0 se Nd0 Nd_ext := NodeStep.trans ha0 hstep4 hstep_s4_se
      have hse_code : se.code = originalRuntimeCode := by
        have := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s4 ecallee) ebody).1
        rw [herun] at this; exact this.trans hs4_code
      have hse_other : ∀ x : MlS, x ≠ ofString "r" → x ≠ ofString "br" → x ≠ ofString "pl" →
          x ≠ ofString "sl" → x ≠ ofString "seg" → se.locals.lookup x = s.locals.lookup x := by
        intro x h1 h2 h3 h4 h5
        simp [se, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, hs4_other x h2 h3 h4 h5]
      refine ⟨Nd_ext, wext, 0, 0, 0, 0,
        hstep_se, hse_code,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_key,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_klen,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vptr,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vlen,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_slot,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_res,
        by simp [se, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_nn,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_ns,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_nl,
        (hse_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_go,
        hwext_root,
        hsl_inv4.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s4_se, hstep_s4_se.sub _ hrin⟩),
        fun h => absurd rfl h⟩
    · rw [if_neg hpl_pos] at hspcont
      dsimp only at hspcont
      have hev_br : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
          (.var .local (ofString "br")) = some (.val (.word wbr)) := hs4_br
      have hubr_set := assign_local_eval_inv hev_br hspcont
      subst hubr_set
      set sb := setVarHOLFinite (ofString "r") (.val (.word wbr)) s4
      have hsb_other : ∀ x : MlS, x ≠ ofString "r" → x ≠ ofString "br" → x ≠ ofString "pl" →
          x ≠ ofString "sl" → x ≠ ofString "seg" → sb.locals.lookup x = s.locals.lookup x := by
        intro x h1 h2 h3 h4 h5
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, hs4_other x h2 h3 h4 h5]
      exact ⟨Nd_sp, wbr, 0, 0, 0, 0,
        hstep4.with_locals_clock _ _, hs4_code,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_key,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_klen,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vptr,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vlen,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_slot,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_res,
        by simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_nn,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_ns,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_nl,
        (hsb_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_go,
        hwbr_root,
        hsl_inv4,
        fun h => absurd rfl h⟩


/-! ## 6. Branch Case (`k == 3`), Full `insSelect_step`, `insBody_step`, Loop Induction & `mpt_insert_node_spec` -/

/-- Branch case (`k == 3`) after `node_invalidate`: proves `InsSelectPost`. -/
theorem insBranch_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Nd0 Nd : List Nat}
    {wkey wklen wvptr wvlen wnode wslot wlevel wres : BitVec 64}
    {u : PanSemStateFiniteExact 64 F}
    (ha0 : ArenaReady s0)
    (hstep : NodeStep s0 s Nd0 Nd)
    (hsc : s.code = originalRuntimeCode)
    (hnode_in : wnode.toNat ∈ Nd)
    (hnode_k3 : memW s wnode.toNat = 3)
    (hle : wlevel.toNat ≤ wklen.toNat)
    (hvlt : wvlen.toNat < 2 ^ 40)
    (hklt : wklen.toNat ≤ 64)
    (hkey : KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat))
    (hsl_inv : wslot = 0 ∨ (ValidSlot s Nd wslot.toNat ∧ wres.toNat ∈ Nd))
    (hs_key : s.locals.lookup (ofString "key") = some (.val (.word wkey)))
    (hs_klen : s.locals.lookup (ofString "klen") = some (.val (.word wklen)))
    (hs_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word wvptr)))
    (hs_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word wvlen)))
    (hs_node : s.locals.lookup (ofString "node") = some (.val (.word wnode)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word wslot)))
    (hs_level : s.locals.lookup (ofString "level") = some (.val (.word wlevel)))
    (hs_res : s.locals.lookup (ofString "result") = some (.val (.word wres)))
    (hs_nn : s.locals.lookup (ofString "next_node") = some (.val (.word 0)))
    (hs_ns : s.locals.lookup (ofString "next_slot") = some (.val (.word 0)))
    (hs_nl : s.locals.lookup (ofString "next_level") = some (.val (.word 0)))
    (hs_go : s.locals.lookup (ofString "go") = some (.val (.word 0)))
    (hrun : evaluateHOLFiniteState s insBranch = (none, u)) :
    InsSelectPost s0 u Nd0 wkey wklen wvptr wvlen wslot wres := by
  rw [insBranch_eq, evaluateHOLFiniteState_ite] at hrun
  have hc_lv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen"))) =
      some (.val (.word (if wlevel = wklen then 1 else 0))) := by
    simp [evalHOLExact, hs_level, hs_klen, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc_lv] at hrun
  by_cases hlv_eq : wlevel = wklen
  · -- Payload arm (`level == klen`): `st node + 160, vptr; st node + 168, vlen; r = node`
    rw [if_pos hlv_eq] at hrun
    simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hrun
    obtain ⟨hdom160, hdom168, hstep_val, _⟩ :=
      branch_store_value_step (wvptr := wvptr) (wvlen := wvlen) hstep.arena hstep.heap hnode_in hnode_k3 hvlt
    set m1 := Wave8Contracts.M26.updW s.memory (wnode + BitVec.ofNat 64 160) wvptr
    set m2 := Wave8Contracts.M26.updW m1 (wnode + BitVec.ofNat 64 168) wvlen
    obtain ⟨b1, hb1, hr1⟩ := seq_none_inv hrun
    have hb1_eq : b1 = { s with memory := m1 } := by
      rw [evaluateHOLFiniteState_store] at hb1
      have hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .local (ofString "node"), .const 160]) =
          some (.val (.word (wnode + BitVec.ofNat 64 160))) := by
        simp [evalHOLExact, evalListHOLExact, hs_node, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "vptr")) = some (.val (.word wvptr)) := hs_vptr
      rw [hd, he] at hb1
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom160, ↓reduceIte] at hb1
      injection hb1 with _ heq; exact heq.symm
    subst hb1_eq
    obtain ⟨b2, hb2, hr2⟩ := seq_none_inv hr1
    have hb2_eq : b2 = { s with memory := m2 } := by
      rw [evaluateHOLFiniteState_store] at hb2
      have hd : @evalHOLExact 64 F _ ({ s with memory := m1 } : PanSemStateFiniteExact 64 F).toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .local (ofString "node"), .const 168]) =
          some (.val (.word (wnode + BitVec.ofNat 64 168))) := by
        simp [evalHOLExact, evalListHOLExact, hs_node, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ ({ s with memory := m1 } : PanSemStateFiniteExact 64 F).toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "vlen")) = some (.val (.word wvlen)) := hs_vlen
      rw [hd, he] at hb2
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom168, ↓reduceIte] at hb2
      injection hb2 with _ heq; exact heq.symm
    subst hb2_eq
    have hev_nd : @evalHOLExact 64 F _ ({ s with memory := m2 } : PanSemStateFiniteExact 64 F).toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "node")) = some (.val (.word wnode)) := hs_node
    have hu_eq := assign_local_eval_inv hev_nd hr2
    subst hu_eq
    set bf := setVarHOLFinite (ofString "r") (.val (.word wnode)) { s with memory := m2 }
    have hstep_s_bf : NodeStep s bf Nd Nd := hstep_val.with_locals_clock bf.locals bf.clock
    have hbf_other : ∀ x : MlS, x ≠ ofString "r" → bf.locals.lookup x = s.locals.lookup x := by
      intro x hx
      simp [bf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
    exact ⟨Nd, wnode, 0, 0, 0, 0,
      NodeStep.trans ha0 hstep hstep_s_bf, hsc,
      (hbf_other _ (by decide)).trans hs_key,
      (hbf_other _ (by decide)).trans hs_klen,
      (hbf_other _ (by decide)).trans hs_vptr,
      (hbf_other _ (by decide)).trans hs_vlen,
      (hbf_other _ (by decide)).trans hs_slot,
      (hbf_other _ (by decide)).trans hs_res,
      by simp [bf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      (hbf_other _ (by decide)).trans hs_nn,
      (hbf_other _ (by decide)).trans hs_ns,
      (hbf_other _ (by decide)).trans hs_nl,
      (hbf_other _ (by decide)).trans hs_go,
      Or.inr hnode_in,
      hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_bf, hrin⟩),
      fun h => absurd rfl h⟩
  · -- Descent arm (`level < klen`): `dec idx = loadByte(key + level); r = node; next_node = ...; next_slot = ...; next_level = level + 1; go = 1`
    rw [if_neg hlv_eq] at hrun
    simp only [↓reduceIte] at hrun
    have hlv_lt : wlevel.toNat < wklen.toNat := by
      apply Nat.lt_of_le_of_ne hle
      intro heq; exact hlv_eq (BitVec.eq_of_toNat_eq heq)
    obtain ⟨hk_sub_nat, hkey_bv⟩ := keyIn_suffix_bv hle hkey
    have hev_kl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]) =
        some (.val (.word (wkey + wlevel))) := by
      simp [evalHOLExact, evalListHOLExact, hs_key, hs_level, valueIsWord, valueWord, wordOpHOL, wordOp]
    obtain ⟨widx, hlb_idx, hwidx_lt⟩ := eval_loadByte_nibble hstep.arena.1 hkey_bv
      (by rw [hk_sub_nat]; omega) hev_kl
    obtain ⟨vidx, u_idx, hev_idx, hr_idx, hu_eq⟩ := dec_none_inv hrun
    have hvidx : vidx = .val (.word widx) := Option.some.inj (hev_idx.symm.trans hlb_idx)
    subst hvidx
    suffices hidx_post : InsSelectPost s0 u_idx Nd0 wkey wklen wvptr wvlen wslot wres by
      rw [hu_eq]
      exact hidx_post.restore_local (by decide)
    set s1 := setVarHOLFinite (ofString "idx") (.val (.word widx)) s
    have hs1_node : s1.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_node,
        show ofString "idx" ≠ ofString "node" by decide]
    obtain ⟨d1, hd1, hr1⟩ := seq_none_inv hr_idx
    have hd1_eq := assign_local_eval_inv (w := wnode) (by exact hs1_node) hd1
    subst hd1_eq
    set d1 := setVarHOLFinite (ofString "r") (.val (.word wnode)) s1
    have hd1_node : d1.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [d1, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_node,
        show ofString "r" ≠ ofString "node" by decide, show ofString "idx" ≠ ofString "node" by decide]
    have hd1_idx : d1.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
      simp [d1, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "r" ≠ ofString "idx" by decide]
    -- Evaluate `load .one (node + 32 + idx * 8)` on `d1`
    have hsz3 : nodeSize (memW s wnode.toNat) = 176 := by simp [nodeSize, hnode_k3]
    have hins_nd := (hstep.heap.1 wnode.toNat hnode_in).2.2.1
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hslot_off_lt : 32 + 8 * widx.toNat < 176 := by omega
    have hslot_bv_eq : wnode + (32 : BitVec 64) + widx * (8 : BitVec 64) =
        wnode + BitVec.ofNat 64 (32 + 8 * widx.toNat) := by
      apply BitVec.eq_of_toNat_eq
      dsimp [Inside, nodeIvl] at hins_nd
      have h32 : (32 : BitVec 64).toNat = 32 := by decide
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h32, h8]
      omega
    have hslot_exp_ev : ∀ {st : PanSemStateFiniteExact 64 F},
        st.locals.lookup (ofString "node") = some (.val (.word wnode)) →
        st.locals.lookup (ofString "idx") = some (.val (.word widx)) →
        @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "node"), .const 32,
            .panop .mul [.var .local (ofString "idx"), .const 8]]) =
          some (.val (.word (wnode + 32 + widx * 8))) := by
      intro st hl_n hl_i
      have hadd0 : ∀ x : BitVec 64, x + (0 : BitVec 64) = x := BitVec.add_zero
      simp only [evalHOLExact, evalListHOLExact, hl_n, hl_i, valueIsWord, valueWord,
        wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
        List.foldr, hadd0]
      congr 3
      exact (BitVec.add_assoc wnode 32 (widx * 8)).symm
    obtain ⟨hev_ch0, hwch_nat⟩ := eval_load_node_field (st := d1) hstep.heap hnode_in hd1_node
      (32 + 8 * widx.toNat) (by change 32 + 8 * widx.toNat < nodeSize (memW s wnode.toNat); omega) (by omega)
    have eval_load_congr : ∀ {e1 e2 : ExpHOL 64} {wa : BitVec 64},
        @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a)) e1 =
          some (.val (.word wa)) →
        @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a)) e2 =
          some (.val (.word wa)) →
        @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a)) (.load .one e1) =
          @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a)) (.load .one e2) := by
      intro e1 e2 wa he1 he2
      unfold evalHOLExact
      rw [he1, he2]
    have hev_ch : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "node"), .const 32,
          .panop .mul [.var .local (ofString "idx"), .const 8]])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + (32 + 8 * widx.toNat)))))) := by
      have h1 := hslot_exp_ev hd1_node hd1_idx
      have h2 : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
          (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 (32 + 8 * widx.toNat))]) =
          some (.val (.word (wnode + 32 + widx * 8))) := by
        rw [hslot_bv_eq]
        simp [evalHOLExact, evalListHOLExact, hd1_node, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [eval_load_congr h1 h2]
      exact hev_ch0
    obtain ⟨d2, hd2, hr2⟩ := seq_none_inv hr1
    have hd2_eq := assign_local_eval_inv hev_ch hd2
    subst hd2_eq
    set wch := BitVec.ofNat 64 (memW s (wnode.toNat + (32 + 8 * widx.toNat)))
    set d2 := setVarHOLFinite (ofString "next_node") (.val (.word wch)) d1
    have hd2_node : d2.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd1_node,
        show ofString "next_node" ≠ ofString "node" by decide]
    have hd2_idx : d2.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
      simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd1_idx,
        show ofString "next_node" ≠ ofString "idx" by decide]
    obtain ⟨d3, hd3, hr3⟩ := seq_none_inv hr2
    have hd3_eq := assign_local_eval_inv (hslot_exp_ev hd2_node hd2_idx) hd3
    subst hd3_eq
    set d3 := setVarHOLFinite (ofString "next_slot") (.val (.word (wnode + 32 + widx * 8))) d2
    have hd3_level : d3.locals.lookup (ofString "level") = some (.val (.word wlevel)) := by
      simp [d3, d2, d1, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_level,
        show ofString "next_slot" ≠ ofString "level" by decide,
        show ofString "next_node" ≠ ofString "level" by decide,
        show ofString "r" ≠ ofString "level" by decide,
        show ofString "idx" ≠ ofString "level" by decide]
    obtain ⟨d4, hd4, hr4⟩ := seq_none_inv hr3
    have hev_nl : @evalHOLExact 64 F _ d3.toExact (fun a => Classical.propDecidable (d3.memaddrs a))
        (.op .add [.var .local (ofString "level"), .const 1]) =
        some (.val (.word (wlevel + 1))) := by
      simp [evalHOLExact, evalListHOLExact, hd3_level, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hd4_eq := assign_local_eval_inv hev_nl hd4
    subst hd4_eq
    set d4 := setVarHOLFinite (ofString "next_level") (.val (.word (wlevel + 1))) d3
    have hd5_eq := assign_local_eval_inv (w := 1) rfl hr4
    subst hd5_eq
    set df := setVarHOLFinite (ofString "go") (.val (.word 1)) d4
    have hdf_other : ∀ x : MlS,
        x ≠ ofString "go" → x ≠ ofString "next_level" → x ≠ ofString "next_slot" →
        x ≠ ofString "next_node" → x ≠ ofString "r" → x ≠ ofString "idx" →
        df.locals.lookup x = s.locals.lookup x := by
      intro x h1 h2 h3 h4 h5 h6
      simp [df, d4, d3, d2, d1, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]
    have hstep_s_df : NodeStep s df Nd Nd :=
      (NodeStep.refl hstep.arena hstep.heap).with_locals_clock df.locals df.clock
    refine ⟨Nd, wnode, wch, wnode + 32 + widx * 8, wlevel + 1, 1,
      hstep.with_locals_clock df.locals df.clock, hsc,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_key,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_klen,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vptr,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_vlen,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_slot,
      (hdf_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs_res,
      by simp [df, d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "r" by decide,
           show ofString "next_level" ≠ ofString "r" by decide,
           show ofString "next_slot" ≠ ofString "r" by decide,
           show ofString "next_node" ≠ ofString "r" by decide],
      by simp [df, d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_node" by decide,
           show ofString "next_level" ≠ ofString "next_node" by decide,
           show ofString "next_slot" ≠ ofString "next_node" by decide],
      by simp [df, d4, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_slot" by decide,
           show ofString "next_level" ≠ ofString "next_slot" by decide],
      by simp [df, d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
           show ofString "go" ≠ ofString "next_level" by decide],
      by simp [df, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      Or.inr hnode_in,
      hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_df, hrin⟩),
      ?_⟩
    intro _
    have h1_nat : (1 : BitVec 64).toNat = 1 := rfl
    have hnl_nat : (wlevel + (1 : BitVec 64)).toNat = wlevel.toNat + 1 := by
      rw [BitVec.toNat_add, h1_nat, Nat.mod_eq_of_lt (by omega)]
    have hns_nat : (wnode + (32 : BitVec 64) + widx * (8 : BitVec 64)).toNat =
        wnode.toNat + 32 + 8 * widx.toNat := by
      rw [hslot_bv_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      dsimp [Inside, nodeIvl] at hins_nd
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hns_nz : wnode + (32 : BitVec 64) + widx * (8 : BitVec 64) ≠ 0 := by
      intro hz; have := congrArg BitVec.toNat hz
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [hns_nat, h0] at this; omega
    have hwch_nat_s : (BitVec.ofNat 64 (memW s (wnode.toNat + (32 + 8 * widx.toNat)))).toNat =
        memW s (wnode.toNat + (32 + 8 * widx.toNat)) := hwch_nat
    have hwch_root : RootIn Nd wch.toNat := by
      have heq_a : wnode.toNat + (32 + 8 * widx.toNat) = wnode.toNat + 32 + 8 * widx.toNat := by omega
      dsimp only [wch]
      rw [hwch_nat_s, heq_a]
      exact (hstep.heap.1 wnode.toNat hnode_in).2.2.2.2.2.1 hnode_k3 widx.toNat hwidx_lt
    have hkey_df : KeyIn df Nd (wkey.toNat + (wlevel + 1).toNat) (wklen.toNat - (wlevel + 1).toNat) := by
      rw [hnl_nat]
      by_cases hrem0 : wklen.toNat - (wlevel.toNat + 1) = 0
      · exact Or.inl hrem0
      · have hlen_nz : wklen.toNat - wlevel.toNat ≠ 0 := by omega
        obtain ⟨_, _, hins, _⟩ := hkey.resolve_left hlen_nz
        have hsub_s : KeyIn s Nd ((BitVec.ofNat 64 (wkey.toNat + wlevel.toNat) + BitVec.ofNat 64 1).toNat)
            (wklen.toNat - (wlevel.toNat + 1)) :=
          keyIn_subslice hkey (by omega)
        have hpo : (BitVec.ofNat 64 (wkey.toNat + wlevel.toNat) + BitVec.ofNat 64 1).toNat =
            wkey.toNat + (wlevel.toNat + 1) := by
          dsimp [Inside] at hins
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        rw [hpo] at hsub_s
        exact hstep_s_df.keyIn hstep.arena hstep.heap hsub_s
    have hvslot_ns : ValidSlot df Nd (wnode + 32 + widx * 8).toNat :=
      ⟨wnode.toNat, hnode_in, Or.inr ⟨hnode_k3, widx.toNat, hwidx_lt, hns_nat⟩⟩
    exact ⟨by rw [hnl_nat]; omega, hwch_root, hkey_df, hvslot_ns, hns_nz, hnode_in⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards

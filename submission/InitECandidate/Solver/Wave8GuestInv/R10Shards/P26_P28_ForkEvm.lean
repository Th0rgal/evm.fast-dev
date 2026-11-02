import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_InitProofs

/-! Proofs of `wk_fork_init` and `wk_evm_init` for Shards P27 + P28. -/

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Loop & `dec` / `decCall` Helpers for `fork_init` and `evm_init` -/

theorem initEff_dec_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (nm : MlS) (c : BitVec 64) {body : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.dec nm .one (.const c) body)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.dec nm .one (.const c) body)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.dec nm .one (.const c) body)).1)
    (hbody : let s' := setVarHOLFinite nm (.val (.word c)) cur
      InitEff s s' Rl B gw →
      (evaluateHOLFiniteState s' body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s' body).1 = none ∨ Resumes (evaluateHOLFiniteState s' body).1) →
      InitEff s (evaluateHOLFiniteState s' body).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.dec nm .one (.const c) body)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_dec_total] at hnt hor ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hor ⊢
  have heff' : InitEff s (setVarHOLFinite nm (.val (.word c)) cur) Rl B gw := heff.locals_clock _ _
  exact (hbody heff' hnt hor).locals_clock _ _

theorem byteEff_counted_storeByte_loop {F : Type}
    (k : Nat) (s : PanSemStateFiniteExact 64 F)
    (p iw limw : BitVec 64) (sz : Nat)
    (addrExp valExp : ExpHOL 64)
    (hk : s.clock ≤ k)
    (hG : GuestInv s)
    (hlim : limw.toNat ≤ 32)
    (hp_hi : p.toNat + sz ≤ heapEnd)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hi_le : iw.toNat ≤ limw.toNat)
    (haddr : ∀ (t : PanSemStateFiniteExact 64 F) (iv : BitVec 64),
      t.globals = s.globals →
      t.locals.lookup (ofString "i") = some (.val (.word iv)) →
      iv.toNat < limw.toNat →
      ∃ off : Nat, off < sz ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) addrExp =
          some (.val (.word (p + BitVec.ofNat 64 off)))) :
    let lp := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const limw))
      (.seq (.storeByte addrExp valExp)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    ByteEff s (evaluateHOLFiniteState s lp).2 [(p.toNat, sz)] := by
  induction k generalizing s iw with
  | zero =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact (ByteEff.refl s _).locals_clock _ _
        · omega
      · exact ByteEff.refl s _
    · exact ByteEff.refl s _
  | succ k ih =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hnz
        split
        · exact (ByteEff.refl s _).locals_clock _ _
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hlt_lim : iw.toNat < limw.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp only [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small iw limw (by omega) (by omega)] at hcond
            by_cases hlt : iw.toNat < limw.toNat
            · exact hlt
            · simp [hlt] at hcond; exact absurd hcond.symm hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          obtain ⟨off, hoff, hev_addr⟩ := haddr sd iw rfl hi hlt_lim
          have hin_sz : 0 < sz → ∃ ivl ∈ [(p.toNat, sz)], ivl.1 ≤ p.toNat ∧ p.toNat + sz ≤ ivl.1 + ivl.2 :=
            fun _ => ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
          have heff_sb := byteEff_storeByte_at hGd addrExp valExp p off sz hp_hi hin_sz hoff hev_addr
          have hcf := evaluate_storeByte_control_frame sd addrExp valExp
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hsb : evaluateHOLFiniteState sd (.storeByte addrExp valExp) with ⟨r1, m1⟩
          rw [hsb] at heff_sb hcf
          cases r1 with
          | some _ =>
            rcases hcf.1 with h | h <;> simp at h; subst h
            exact ((ByteEff.refl s _).locals_clock _ _).trans heff_sb
          | none =>
            dsimp only
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
              rw [hcf.2.2.1]; exact hi
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn]; dsimp only
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1))) m1
            have heff_m2 : ByteEff s m2 [(p.toNat, sz)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_sb).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 1))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hi1_le : (iw + 1).toNat ≤ limw.toNat := by
              have : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
              omega
            have hm2_clk : m2.clock ≤ k := by
              change m1.clock ≤ k; rw [hcf.2.1]; change s.clock - 1 ≤ k; omega
            exact heff_m2.trans (ih m2 (iw + 1) hm2_clk hGm2 hi_m2 hi1_le
              (fun t iv htg hti hlt' => haddr t iv (htg.trans heff_m2.globals) hti hlt'))
      · exact ByteEff.refl s _
    · exact ByteEff.refl s _

/-! ## 2. `wk_fork_init` -/

theorem initEff_alloc_and_addr_from_words {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (hi4 mid8 lo8 : BitVec 64) {rest : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hgb_mem : (gname, 24) ∈ globalBuffers)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_mem : ofString gname ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString gname), .const hi4, .const mid8, .const lo8])
          rest))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString gname), .const hi4, .const mid8, .const lo8])
          rest))).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [.const 24])
          (.seq (.call (some (none, none)) (ofString "addr_from_words")
              [.var .global (ofString gname), .const hi4, .const mid8, .const lo8])
            rest))).1)
    (hrest : ∀ mid : PanSemStateFiniteExact 64 F,
      InitEff s mid Rl B gw →
      (evaluateHOLFiniteState mid rest).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid rest).1 = none ∨ Resumes (evaluateHOLFiniteState mid rest).1) →
      InitEff s (evaluateHOLFiniteState mid rest).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString gname), .const hi4, .const mid8, .const lo8])
          rest))).2 Rl B gw := by
  refine initEff_seq_alloc_global gname 24 (.const 24) heff
    ⟨by omega, by omega⟩ rfl hgb_mem hgw_hp hgw_mem hnt hor
    (fun s1 pw _ _ heff1 hpw_g _ hpw_lo hpw_hi hnt1 hor1 => ?_)
  have hpw_lim : pw.toNat + 24 ≤ heapLimit := le_trans hpw_hi heff1.arena.2.2.1
  refine initEff_seq hnt1 hor1 (fun hnt_a hor_a => ?_) (fun s2 _ heff2 hnt2 hor2 => hrest s2 heff2 hnt2 hor2)
  have hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .global (ofString gname), .const hi4, .const mid8, .const lo8] =
      some [.val (.word pw), .val (.word hi4), .val (.word mid8), .val (.word lo8)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpw_g]
  have hb := call0_byteEff funByteEff_addr_from_words s1 _ [(pw.toNat, 20)] heff1.code heff1.arena.1
    (fun vs hvs iv hiv _ => by
      rw [hargs] at hvs; injection hvs with hvs; subst hvs
      simp [valWordNat] at hiv; subst hiv
      exact ⟨(pw.toNat, 20), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
    hnt_a hor_a
  exact heff1.of_byteEff hb (fun iv hiv _ => by
    simp at hiv; subst hiv
    exact Or.inr (Or.inr ⟨hpw_lo, by omega⟩))

theorem wk_fork_init :
    WorldKeeps WorldOK
      (fun s =>
        [(globN s "beacon_roots_address", if globN s "beacon_roots_address" = 0 then 0 else 24),
         (globN s "builder_deposit_address", if globN s "builder_deposit_address" = 0 then 0 else 24),
         (globN s "builder_exit_address", if globN s "builder_exit_address" = 0 then 0 else 24),
         (globN s "consolidation_request_address", if globN s "consolidation_request_address" = 0 then 0 else 24),
         (globN s "deposit_contract_address", if globN s "deposit_contract_address" = 0 then 0 else 24),
         (globN s "deposit_event_signature_hash", if globN s "deposit_event_signature_hash" = 0 then 0 else 32),
         (globN s "history_storage_address", if globN s "history_storage_address" = 0 then 0 else 24),
         (globN s "precompile_addrs", if globN s "precompile_addrs" = 0 then 0 else 360),
         (globN s "withdrawal_request_address", if globN s "withdrawal_request_address" = 0 then 0 else 24),
         (globN s "zero32", if globN s "zero32" = 0 then 0 else 32)])
      ["beacon_roots_address", "builder_deposit_address", "builder_exit_address",
       "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash",
       "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"]
      stdKeep NoExtra (ofString "fork_init") := by
  refine ⟨_, _, _, lookup_fork_init, fun {F} s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_fork_init =
      .seq (.call (some (some (.global, ofString "zero32"), none)) (ofString "alloc") [.const 32])
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "zero32"), .const 32])
      (.seq (.call (some (some (.global, ofString "precompile_addrs"), none)) (ofString "alloc")
          [.panop .mul [.const 18, .const 20]])
      (.seq (.call (some (none, none)) (ofString "memzero")
          [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]])
      (.dec (ofString "i") .one (.const 0)
        (.seq (.while (.cmp .less (.var .local (ofString "i")) (.const 17))
            (.seq (.storeByte (.op .add [.var .global (ofString "precompile_addrs"),
                  .panop .mul [.var .local (ofString "i"), .const 20], .const 19])
                (.op .add [.var .local (ofString "i"), .const 1]))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        (.seq (.storeByte (.op .add [.var .global (ofString "precompile_addrs"),
              .panop .mul [.const 17, .const 20], .const 18]) (.const 1))
        (.seq (.call (some (some (.global, ofString "beacon_roots_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "beacon_roots_address"), .const 998902, .const 15506597749690834871, .const 13311379508201171970])
        (.seq (.call (some (some (.global, ofString "history_storage_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "history_storage_address"), .const 63752, .const 2878298490047003138, .const 3700577164601600309])
        (.seq (.call (some (some (.global, ofString "withdrawal_request_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "withdrawal_request_address"), .const 2401, .const 17242047345525313946, .const 15579492241104728066])
        (.seq (.call (some (some (.global, ofString "consolidation_request_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "consolidation_request_address"), .const 48093, .const 14397524800236640159, .const 10016273463683084881])
        (.seq (.call (some (some (.global, ofString "builder_deposit_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "builder_deposit_address"), .const 49140, .const 7603452151126424148, .const 760111669195932290])
        (.seq (.call (some (some (.global, ofString "builder_exit_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "builder_exit_address"), .const 25814, .const 8669529151676140297, .const 4307224735379260034])
        (.seq (.call (some (some (.global, ofString "deposit_contract_address"), none)) (ofString "alloc") [.const 24])
        (.seq (.call (some (none, none)) (ofString "addr_from_words")
            [.var .global (ofString "deposit_contract_address"), .const 0, .const 2421447037043915651, .const 11294470620239562234])
        (.seq (.call (some (some (.global, ofString "deposit_event_signature_hash"), none)) (ofString "alloc") [.const 32])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const 0], .const 7249595157780304706])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const 8], .const 12676030261858484297])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const 16], .const 16708898399860066458])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const 24], .const 12074291595689605317])
          (.return (.const 0))))))))))))))))))))))))))) := rfl
  rw [hbody] at hnt hres ⊢
  let Rlfork : List Ivl :=
    [(globN s "beacon_roots_address", if globN s "beacon_roots_address" = 0 then 0 else 24),
     (globN s "builder_deposit_address", if globN s "builder_deposit_address" = 0 then 0 else 24),
     (globN s "builder_exit_address", if globN s "builder_exit_address" = 0 then 0 else 24),
     (globN s "consolidation_request_address", if globN s "consolidation_request_address" = 0 then 0 else 24),
     (globN s "deposit_contract_address", if globN s "deposit_contract_address" = 0 then 0 else 24),
     (globN s "deposit_event_signature_hash", if globN s "deposit_event_signature_hash" = 0 then 0 else 32),
     (globN s "history_storage_address", if globN s "history_storage_address" = 0 then 0 else 24),
     (globN s "precompile_addrs", if globN s "precompile_addrs" = 0 then 0 else 360),
     (globN s "withdrawal_request_address", if globN s "withdrawal_request_address" = 0 then 0 else 24),
     (globN s "zero32", if globN s "zero32" = 0 then 0 else 32)]
  let gwfork : List String :=
    ["beacon_roots_address", "builder_deposit_address", "builder_exit_address",
     "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash",
     "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"]
  let heff0 := InitEff.refl s Rlfork [] gwfork hWOK.1 hc
  -- 1. `zero32 := alloc(32); memzero(zero32, 32)`
  refine initEff_seq_alloc_global "zero32" 32 (.const 32) heff0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt (Or.inr hres)
    (fun s1 pz32 _ _ heff1 hpz32_1 _ hpz32_lo hpz32_hi hnt1 hor1 => ?_)
  have hz32_lim : pz32.toNat + 32 ≤ heapLimit := le_trans hpz32_hi heff1.arena.2.2.1
  refine initEff_seq hnt1 hor1
    (fun hnt_mz1 hor_mz1 => by
      have hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.var .global (ofString "zero32"), .const 32] = some [.val (.word pz32), .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpz32_1]
      have hb := call0_byteEff funByteEff_memzero s1 _ [(pz32.toNat, 32)] heff1.code heff1.arena.1
        (fun vs hvs iv hiv _ => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hiv; subst hiv
          exact ⟨(pz32.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        hnt_mz1 hor_mz1
      exact heff1.of_byteEff hb (fun iv hiv _ => by
        simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpz32_lo, hz32_lim⟩)))
    (fun s2 _ heff2 hnt2 hor2 => ?_)
  -- 2. `precompile_addrs := alloc(18 * 20); memzero(precompile_addrs, 18 * 20)`
  refine initEff_seq_alloc_global "precompile_addrs" 360 (.panop .mul [.const 18, .const 20]) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 ppa _ _ heff3 hppa3 _ hppa_lo hppa_hi hnt3 hor3 => ?_)
  have hpa_lim : ppa.toNat + 360 ≤ heapLimit := le_trans hppa_hi heff3.arena.2.2.1
  have hmz_pa_eff : (evaluateHOLFiniteState s3
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]])).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s3
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]])).1 = none ∨
      Resumes (evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "memzero")
          [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]])).1) →
    ByteEff s3 (evaluateHOLFiniteState s3
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]])).2
      [(ppa.toNat, 360)] := by
    intro hnt_m hor_m
    have hargs : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
        [.var .global (ofString "precompile_addrs"), .panop .mul [.const 18, .const 20]] =
        some [.val (.word ppa), .val (.word 360)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hppa3,
        panOpHOL, valueIsWord, valueWord]
    exact call0_byteEff funByteEff_memzero s3 _ [(ppa.toNat, 360)] heff3.code heff3.arena.1
      (fun vs hvs iv hiv _ => by
        rw [hargs] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hiv; subst hiv
        exact ⟨(ppa.toNat, 360), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt_m hor_m
  refine initEff_seq hnt3 hor3
    (fun hnt_m hor_m => heff3.of_byteEff (hmz_pa_eff hnt_m hor_m) (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hppa_lo, hpa_lim⟩)))
    (fun s4 hs4 heff4 hnt4 hor4 => ?_)
  have hs4_glob : s4.globals = s3.globals := by
    obtain ⟨hnt_m, hor_m⟩ := seq_nt_or s3 _ _ hnt3 hor3
    have hb := hmz_pa_eff hnt_m hor_m
    rw [hs4] at hb; exact hb.globals
  have hppa4 : s4.globals.lookup (ofString "precompile_addrs") = some (.val (.word ppa)) := by
    rw [hs4_glob]; exact hppa3
  -- 3. `dec "i" 0`: loop `i < 17` + `storeByte (precompile_addrs + 17*20 + 18) 1`
  refine initEff_dec_const (ofString "i") 0 heff4 hnt4 hor4 (fun heff5 hnt5 hor5 => ?_)
  let s5 := setVarHOLFinite (ofString "i") (.val (.word 0)) s4
  have hppa5 : s5.globals.lookup (ofString "precompile_addrs") = some (.val (.word ppa)) := hppa4
  have hi5 : s5.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlp_eff := byteEff_counted_storeByte_loop s5.clock s5 ppa 0 17 360
    (.op .add [.var .global (ofString "precompile_addrs"),
      .panop .mul [.var .local (ofString "i"), .const 20], .const 19])
    (.op .add [.var .local (ofString "i"), .const 1])
    le_rfl heff5.arena.1 (by decide) (le_trans hpa_lim hhl_he) hi5 (by decide)
    (fun t iv htg hti hlt => by
      have hp_t : t.globals.lookup (ofString "precompile_addrs") = some (.val (.word ppa)) := by
        rw [htg]; exact hppa5
      have h17 : (17 : BitVec 64).toNat = 17 := rfl
      rw [h17] at hlt
      refine ⟨iv.toNat * 20 + 19, by omega, ?_⟩
      have hmul_eq : iv * 20#64 + 19#64 = BitVec.ofNat 64 (iv.toNat * 20 + 19) := by
        apply BitVec.eq_of_toNat_eq
        have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
        have h19 : (19#64 : BitVec 64).toNat = 19 := rfl
        have h264_c : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
        have hm : (iv * 20#64).toNat = iv.toNat * 20 := BitVec.toNat_mul_of_lt (by rw [h20]; omega)
        rw [BitVec.toNat_add_of_lt (by rw [hm, h19]; omega), hm, h19, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      simp [evalHOLExact, evalListHOLExact, hp_t, hti, panOpHOL, valueIsWord, valueWord,
        wordOpHOL, wordOp, BitVec.add_assoc]; exact hmul_eq)
  refine initEff_seq hnt5 hor5
    (fun _ _ => heff5.of_byteEff hlp_eff (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hppa_lo, hpa_lim⟩)))
    (fun s6 hs6 heff6 hnt6 hor6 => ?_)
  have hs6_glob : s6.globals = s5.globals := by
    dsimp only at hlp_eff; change evaluateHOLFiniteState s5 _ = (none, s6) at hs6
    rw [hs6] at hlp_eff; exact hlp_eff.globals
  have hppa6 : s6.globals.lookup (ofString "precompile_addrs") = some (.val (.word ppa)) := by
    rw [hs6_glob]; exact hppa5
  -- `storeByte (precompile_addrs + 17*20 + 18) 1`
  have hsb_17 : ByteEff s6 (evaluateHOLFiniteState s6
      (.storeByte (.op .add [.var .global (ofString "precompile_addrs"),
          .panop .mul [.const 17, .const 20], .const 18]) (.const 1))).2 [(ppa.toNat, 360)] := by
    refine byteEff_storeByte_at heff6.arena.1 _ _ ppa 358 360 (le_trans hpa_lim hhl_he)
      (fun _ => ⟨(ppa.toNat, 360), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩) (by omega) ?_
    have h358 : (17 : BitVec 64) * 20 + 18 = BitVec.ofNat 64 358 := rfl
    simp [evalHOLExact, evalListHOLExact, hppa6, panOpHOL, valueIsWord, valueWord,
      wordOpHOL, wordOp, BitVec.add_assoc, h358]
  refine initEff_seq hnt6 hor6
    (fun _ _ => heff6.of_byteEff hsb_17 (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hppa_lo, hpa_lim⟩)))
    (fun s7 _ heff7 hnt7 hor7 => ?_)
  -- 4. Seven `alloc(24) + addr_from_words` pairs!
  refine initEff_alloc_and_addr_from_words "beacon_roots_address" _ _ _ heff7
    (by decide) (by decide) (by decide) hnt7 hor7 (fun s8 heff8 hnt8 hor8 => ?_)
  refine initEff_alloc_and_addr_from_words "history_storage_address" _ _ _ heff8
    (by decide) (by decide) (by decide) hnt8 hor8 (fun s9 heff9 hnt9 hor9 => ?_)
  refine initEff_alloc_and_addr_from_words "withdrawal_request_address" _ _ _ heff9
    (by decide) (by decide) (by decide) hnt9 hor9 (fun s10 heff10 hnt10 hor10 => ?_)
  refine initEff_alloc_and_addr_from_words "consolidation_request_address" _ _ _ heff10
    (by decide) (by decide) (by decide) hnt10 hor10 (fun s11 heff11 hnt11 hor11 => ?_)
  refine initEff_alloc_and_addr_from_words "builder_deposit_address" _ _ _ heff11
    (by decide) (by decide) (by decide) hnt11 hor11 (fun s12 heff12 hnt12 hor12 => ?_)
  refine initEff_alloc_and_addr_from_words "builder_exit_address" _ _ _ heff12
    (by decide) (by decide) (by decide) hnt12 hor12 (fun s13 heff13 hnt13 hor13 => ?_)
  refine initEff_alloc_and_addr_from_words "deposit_contract_address" _ _ _ heff13
    (by decide) (by decide) (by decide) hnt13 hor13 (fun s14 heff14 hnt14 hor14 => ?_)
  -- 5. `deposit_event_signature_hash := alloc(32)` + four `st_be64` calls at `+0, +8, +16, +24`!
  refine initEff_seq_alloc_global "deposit_event_signature_hash" 32 (.const 32) heff14
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt14 hor14
    (fun s15 pde _ _ heff15 hpde15 _ hpde_lo hpde_hi hnt15 hor15 => ?_)
  have hpde_lim : pde.toNat + 32 ≤ heapLimit := le_trans hpde_hi heff15.arena.2.2.1
  have st_be64_step : ∀ (curS : PanSemStateFiniteExact 64 F) (offw val : BitVec 64) {rest : ProgHOL 64},
      offw.toNat + 8 ≤ 32 →
      InitEff s curS Rlfork [] gwfork →
      curS.globals.lookup (ofString "deposit_event_signature_hash") = some (.val (.word pde)) →
      (evaluateHOLFiniteState curS
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw],
             .const val]) rest)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState curS
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw],
             .const val]) rest)).1 = none ∨
        Resumes (evaluateHOLFiniteState curS
          (.seq (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw],
               .const val]) rest)).1) →
      (∀ midS : PanSemStateFiniteExact 64 F,
        InitEff s midS Rlfork [] gwfork →
        midS.globals.lookup (ofString "deposit_event_signature_hash") = some (.val (.word pde)) →
        (evaluateHOLFiniteState midS rest).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState midS rest).1 = none ∨ Resumes (evaluateHOLFiniteState midS rest).1) →
        InitEff s (evaluateHOLFiniteState midS rest).2 Rlfork [] gwfork) →
      InitEff s (evaluateHOLFiniteState curS
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw],
             .const val]) rest)).2 Rlfork [] gwfork := by
    intro curS offw val rest hoff heffS hpdeS hntS horS hcont
    have hargs : evalListHOLFinite curS (h := fun a => Classical.propDecidable (curS.memaddrs a))
        [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw], .const val] =
        some [.val (.word (pde + offw)), .val (.word val)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpdeS, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hadd_off : (pde + offw).toNat = pde.toNat + offw.toNat := BitVec.toNat_add_of_lt (by omega)
    have hb_fn : (evaluateHOLFiniteState curS (.call (some (none, none)) (ofString "st_be64")
        [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw], .const val])).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState curS (.call (some (none, none)) (ofString "st_be64")
        [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw], .const val])).1 = none ∨
        Resumes (evaluateHOLFiniteState curS (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw], .const val])).1) →
      ByteEff curS (evaluateHOLFiniteState curS (.call (some (none, none)) (ofString "st_be64")
        [.op .add [.var .global (ofString "deposit_event_signature_hash"), .const offw], .const val])).2
        [(pde.toNat, 32)] := by
      intro hnt_c hor_c
      exact call0_byteEff funByteEff_st_be64 curS _ [(pde.toNat, 32)] heffS.code heffS.arena.1
        (fun vs hvs iv hiv _ => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, hadd_off] at hiv; subst hiv
          exact ⟨(pde.toNat, 32), List.mem_singleton.2 rfl, by omega, by omega⟩)
        hnt_c hor_c
    refine initEff_seq hntS horS
      (fun hnt_c hor_c => heffS.of_byteEff (hb_fn hnt_c hor_c) (fun iv hiv _ => by
        simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpde_lo, hpde_lim⟩)))
      (fun midS hmidS heffM hntM horM => ?_)
    obtain ⟨hnt_c, hor_c⟩ := seq_nt_or curS _ _ hntS horS
    have hbM := hb_fn hnt_c hor_c
    rw [hmidS] at hbM
    exact hcont midS heffM (by rw [hbM.globals]; exact hpdeS) hntM horM
  refine st_be64_step s15 0 7249595157780304706 (by decide) heff15 hpde15 hnt15 hor15
    (fun s16 heff16 hpde16 hnt16 hor16 => ?_)
  refine st_be64_step s16 8 12676030261858484297 (by decide) heff16 hpde16 hnt16 hor16
    (fun s17 heff17 hpde17 hnt17 hor17 => ?_)
  refine st_be64_step s17 16 16708898399860066458 (by decide) heff17 hpde17 hnt17 hor17
    (fun s18 heff18 hpde18 hnt18 hor18 => ?_)
  refine st_be64_step s18 24 12074291595689605317 (by decide) heff18 hpde18 hnt18 hor18
    (fun s19 heff19 _ _ _ => initEff_return _ heff19)

/-! ## 3. `wk_evm_init` -/

theorem initEff_decCall_heap_mark {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (nm : MlS) {cont : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.decCall nm .one (ofString "heap_mark") [] cont)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.decCall nm .one (ofString "heap_mark") [] cont)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.decCall nm .one (ofString "heap_mark") [] cont)).1)
    (hcont : ∀ (pw : BitVec 64) (next : PanSemStateFiniteExact 64 F),
      cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) →
      next.locals = cur.locals.update (nm, .val (.word pw)) →
      next.globals = cur.globals →
      InitEff s next Rl B gw →
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState next cont).1 = none ∨ Resumes (evaluateHOLFiniteState next cont).1) →
      InitEff s (evaluateHOLFiniteState next cont).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.decCall nm .one (ofString "heap_mark") [] cont)).2 Rl B gw := by
  obtain ⟨pw, hpw⟩ := heff.hp_word
  have hl := pan_zero_arg_lookup cur.code.lookup (ofString "heap_mark")
    (sourceFnBody Guest.Software.guestFn_heap_mark) .one (by rw [heff.code]; exact lookup_heap_mark)
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [] = some [] := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  rw [hl] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  by_cases hz : cur.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt hor ⊢
    have hbody_hm : sourceFnBody Guest.Software.guestFn_heap_mark = .return (.var .global (ofString "heap_ptr")) := rfl
    have hev_hm : evaluateHOLFiniteState (callEntryStateHOLFinite cur HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_heap_mark) =
        (some (.returned (.val (.word pw))),
         emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty)) := by
      rw [hbody_hm, evaluateHOLFiniteState_return]
      simp [callEntryStateHOLFinite, evalHOLExact, hpw, shapeOfHOLExact]
    rw [hev_hm] at hnt hor ⊢
    dsimp only at hnt hor ⊢
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh] at hnt hor ⊢
    let next := setVarHOLFinite nm (.val (.word pw))
      { emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty) with locals := cur.locals }
    have hnext_eq : next = { cur with locals := cur.locals.update (nm, .val (.word pw)), clock := cur.clock - 1 } := rfl
    exact (hcont pw next hpw (by rw [hnext_eq]) (by rw [hnext_eq])
      (by rw [hnext_eq]; exact heff.locals_clock _ _) hnt hor).locals_clock _ _

theorem initEff_decCall_alloc_local {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (nm : MlS) (sz : Nat) {cont : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hsz_bound : 0 < sz ∧ sz ≤ 8192)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur (.decCall nm .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.decCall nm .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.decCall nm .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1)
    (hcont : ∀ (pw q : BitVec 64) (next : PanSemStateFiniteExact 64 F),
      cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) →
      pw.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + sz ≤ q.toNat →
      q.toNat ≤ heapLimit →
      next.locals = cur.locals.update (nm, .val (.word pw)) →
      next.globals = cur.globals.update (ofString "heap_ptr", .val (.word q)) →
      InitEff s next Rl B gw →
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState next cont).1 = none ∨ Resumes (evaluateHOLFiniteState next cont).1) →
      InitEff s (evaluateHOLFiniteState next cont).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.decCall nm .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).2 Rl B gw := by
  obtain ⟨pw, hpw⟩ := heff.hp_word
  have hl := pan_one_word_lookup cur.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (BitVec.ofNat 64 sz)
    (by rw [heff.code]; exact lookup_alloc)
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
      [.const (BitVec.ofNat 64 sz)] = some [.val (.word (BitVec.ofNat 64 sz))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  rw [hl] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  by_cases hz : cur.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt hor ⊢
    let entry := callEntryStateHOLFinite cur
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz))))
    have hres_entry : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
      rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
      dsimp only [entry] at hb
      rw [hb] at hor
      cases rb with
      | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some rb' =>
        cases rb' with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev =>
          rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
          · simp at h
          · simp at h
          · simp at h; obtain ⟨rfl, _⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
        | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hal := evaluate_alloc_body_resumes entry pw (BitVec.ofNat 64 sz) heff.code hpw
      (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_entry
    dsimp only [entry] at hal
    rcases hb : evaluateHOLFiniteState
      (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz)))))
      (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
    have hnt' := hnt; have hor' := hor
    rw [hb] at hal hnt' hor'
    obtain ⟨rfl, hpb_eq, hcmp2⟩ := hal
    dsimp only at hpb_eq hnt' hor' ⊢
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh] at hnt' hor' ⊢
    let q := (pw + (BitVec.ofNat 64 sz + 7)) &&& ((0 : BitVec 64) - 8)
    have hpw_glob : globN cur "heap_ptr" = pw.toNat := by simp [globN, hpw]
    have hsz_toNat : (BitVec.ofNat 64 sz).toNat = sz := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbnds := alloc_bounds_general pw (BitVec.ofNat 64 sz)
      (by rw [← hpw_glob]; exact heff.arena.2.2.1)
      (by rw [← hpw_glob]; exact heff.arena.2.2.2.2.2.2.1)
      (by rw [hsz_toNat]; exact hsz_bound.2) hcmp2
    dsimp only at hbnds; rw [hsz_toNat] at hbnds
    let next := setVarHOLFinite nm (.val (.word pw)) { pb with locals := cur.locals }
    let nextExplicit : PanSemStateFiniteExact 64 F := { cur with
        locals := cur.locals.update (nm, .val (.word pw)),
        globals := cur.globals.update (ofString "heap_ptr", .val (.word q)),
        clock := pb.clock }
    have hnext_eq : next = nextExplicit := by
      dsimp only [next, nextExplicit, setVarHOLFinite]
      rw [hpb_eq]; rfl
    have hq_ge_pw : pw.toNat ≤ q.toNat := le_trans (Nat.le_add_right _ _) hbnds.1
    have heff_next : InitEff s next Rl B gw := by
      rw [hnext_eq]
      have hhp_n : globN nextExplicit "heap_ptr" = q.toNat := by
        simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE]
      have hfmp_n : globN nextExplicit "frame_mem_ptr" = globN cur "frame_mem_ptr" := by
        simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "heap_ptr" == ofString "frame_mem_ptr") = false by decide]
      have hsp_n : globN nextExplicit "scratch_ptr" = globN cur "scratch_ptr" := by
        simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "heap_ptr" == ofString "scratch_ptr") = false by decide]
      obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8⟩ := heff.arena.2
      refine ⟨⟨guestInv_congr (s := cur) rfl rfl rfl rfl heff.arena.1,
        ⟨by rw [hhp_n]; rw [hpw_glob] at ha1; exact le_trans ha1 hq_ge_pw,
         by rw [hhp_n]; exact hbnds.2.1,
         by rw [hfmp_n]; exact ha3,
         by rw [hfmp_n, hsp_n]; exact ha4,
         by rw [hsp_n]; exact ha5,
         by rw [hhp_n]; exact hbnds.2.2.1,
         by rw [hfmp_n]; exact ha7,
         by rw [hsp_n]; exact ha8⟩⟩,
        heff.code, heff.memaddrs, heff.be, heff.eshapes,
        ⟨q, by simp [nextExplicit, HolFiniteMapExact.lookup_update, FUPDATE]⟩,
        by rw [hhp_n]; have := heff.hp_lo; rw [hpw_glob] at this; exact le_trans this hq_ge_pw,
        hfmp_n.trans heff.fmp_eq, hsp_n.trans heff.sp_eq,
        fun k hk => by
          have hne : (ofString "heap_ptr" == k) = false :=
            beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_hp))
          simp only [nextExplicit, HolFiniteMapExact.lookup_update, FUPDATE, hne, Bool.false_eq_true, ↓reduceIte]
          exact heff.gw_kept k hk,
        ?_, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
      · have hgb_not_hp : ∀ p ∈ globalBuffers, (ofString "heap_ptr" == ofString p.1) = false := by decide
        refine ⟨fun gn hgn => ?_, ?_⟩
        · have hsame : globN nextExplicit gn.1 = globN cur gn.1 := by
            simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp gn hgn]
          rw [hsame, hhp_n]
          rcases heff.fresh_bufs.1 gn hgn with h1 | h2 | ⟨h8, hin1, hin2⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · rw [hpw_glob] at hin2
            exact Or.inr (Or.inr ⟨h8, hin1, le_trans hin2 hq_ge_pw⟩)
        · rw [List.pairwise_iff_getElem]
          have hpw_old := List.pairwise_iff_getElem.1 heff.fresh_bufs.2
          intro i j hi hj hlt ha hb
          have ha_same : globN nextExplicit globalBuffers[i].1 = globN cur globalBuffers[i].1 := by
            simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp _ (List.getElem_mem hi)]
          have hb_same : globN nextExplicit globalBuffers[j].1 = globN cur globalBuffers[j].1 := by
            simp [nextExplicit, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp _ (List.getElem_mem hj)]
          rw [ha_same] at ha ⊢; rw [hb_same] at hb ⊢
          exact hpw_old i j hi hj hlt ha hb
    exact (hcont pw q next hpw hbnds.2.2.2 (by rw [← hpw_glob]; exact heff.hp_lo)
      hbnds.1 hbnds.2.1 (by rw [hnext_eq]) (by rw [hnext_eq]) heff_next hnt' hor').locals_clock _ _

theorem initEff_seq_heap_release {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (markExp : ExpHOL 64) (mw : BitVec 64) {rest : ProgHOL 64}
    (hAs : ArenaOK s)
    (heff : InitEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hm_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) markExp =
      some (.val (.word mw)))
    (hm_lo : globN s "heap_ptr" ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm8 : mw.toNat % 8 = 0)
    (hfb_mark : ∀ gn ∈ globalBuffers,
      globN cur gn.1 = globN s gn.1 ∨ globN cur gn.1 = 0 ∨
      ((globN cur gn.1) % 8 = 0 ∧ Inside (globN cur gn.1, gn.2) (globN s "heap_ptr") mw.toNat))
    (hnt : (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "heap_release") [markExp]) rest)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "heap_release") [markExp]) rest)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.seq (.call (some (none, none)) (ofString "heap_release") [markExp]) rest)).1)
    (hrest : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.locals = cur.locals →
      mid.globals = cur.globals.update (ofString "heap_ptr", .val (.word mw)) →
      InitEff s mid Rl B gw →
      (evaluateHOLFiniteState mid rest).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid rest).1 = none ∨ Resumes (evaluateHOLFiniteState mid rest).1) →
      InitEff s (evaluateHOLFiniteState mid rest).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "heap_release") [markExp]) rest)).2 Rl B gw := by
  obtain ⟨pw_cur, hpw_cur⟩ := heff.hp_word
  obtain ⟨hnt1, hor1⟩ := seq_nt_or cur _ rest hnt hor
  have hl := pan_one_word_lookup cur.code.lookup (ofString "heap_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_heap_release) mw
    (by rw [heff.code]; exact lookup_heap_release)
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [markExp] =
      some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm_ev]
  have hcall_eq : ∃ clk',
      evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [markExp]) =
      (none, { cur with globals := cur.globals.update (ofString "heap_ptr", .val (.word mw)), clock := clk' }) := by
    rw [evaluateHOLFiniteState_call, hargs] at hnt1 ⊢
    dsimp only at hnt1 ⊢
    rw [hl] at hnt1 ⊢
    dsimp only at hnt1 ⊢
    by_cases hz : cur.clock = 0
    · rw [if_pos hz] at hnt1; exact absurd rfl hnt1
    · rw [if_neg hz]
      have hbody_hr : sourceFnBody Guest.Software.guestFn_heap_release =
          .seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
      have hev_hr : evaluateHOLFiniteState
          (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
          (sourceFnBody Guest.Software.guestFn_heap_release) =
          (some (.returned (.val (.word 0))),
           emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw))
             (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))))) := by
        rw [hbody_hr, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [callEntryStateHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
          isValidValueHOLExact, lookupKvarHOLExact, hpw_cur, shapeOfHOLExact, shapeEqHOL,
          setKvarHOLFinite, setGlobalHOLFinite, evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [hev_hr]; dsimp only
      have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh0]
      exact ⟨cur.clock - 1, rfl⟩
  obtain ⟨clk', hcall⟩ := hcall_eq
  rw [evaluateHOLFiniteState_seq_line780, hcall] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  let mid : PanSemStateFiniteExact 64 F :=
    { cur with globals := cur.globals.update (ofString "heap_ptr", .val (.word mw)), clock := clk' }
  have hhp_m : globN mid "heap_ptr" = mw.toNat := by simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hfmp_m : globN mid "frame_mem_ptr" = globN cur "frame_mem_ptr" := by
    simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE, show (ofString "heap_ptr" == ofString "frame_mem_ptr") = false by decide]
  have hsp_m : globN mid "scratch_ptr" = globN cur "scratch_ptr" := by
    simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE, show (ofString "heap_ptr" == ofString "scratch_ptr") = false by decide]
  have hsb_lo : sourceBase ≤ mw.toNat := le_trans hAs.1 hm_lo
  obtain ⟨_, _, ha3, ha4, ha5, _, ha7, ha8⟩ := heff.arena.2
  have heff_mid : InitEff s mid Rl B gw := by
    refine ⟨⟨guestInv_congr (s := cur) rfl rfl rfl rfl heff.arena.1,
      ⟨by rw [hhp_m]; exact hsb_lo, by rw [hhp_m]; exact hm_hi,
       by rw [hfmp_m]; exact ha3, by rw [hfmp_m, hsp_m]; exact ha4, by rw [hsp_m]; exact ha5,
       by rw [hhp_m]; exact hm8, by rw [hfmp_m]; exact ha7, by rw [hsp_m]; exact ha8⟩⟩,
      heff.code, heff.memaddrs, heff.be, heff.eshapes,
      ⟨mw, by simp [mid, HolFiniteMapExact.lookup_update, FUPDATE]⟩,
      by rw [hhp_m]; exact hm_lo,
      hfmp_m.trans heff.fmp_eq, hsp_m.trans heff.sp_eq,
      fun k hk => by
        have hne : (ofString "heap_ptr" == k) = false :=
          beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_hp))
        simp only [mid, HolFiniteMapExact.lookup_update, FUPDATE, hne, Bool.false_eq_true, ↓reduceIte]
        exact heff.gw_kept k hk,
      ?_, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
    · have hgb_not_hp : ∀ p ∈ globalBuffers, (ofString "heap_ptr" == ofString p.1) = false := by decide
      refine ⟨fun gn hgn => ?_, ?_⟩
      · have hsame : globN mid gn.1 = globN cur gn.1 := by
          simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp gn hgn]
        rw [hsame, hhp_m]
        exact hfb_mark gn hgn
      · rw [List.pairwise_iff_getElem]
        have hpw_old := List.pairwise_iff_getElem.1 heff.fresh_bufs.2
        intro i j hi hj hlt ha hb
        have ha_same : globN mid globalBuffers[i].1 = globN cur globalBuffers[i].1 := by
          simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp _ (List.getElem_mem hi)]
        have hb_same : globN mid globalBuffers[j].1 = globN cur globalBuffers[j].1 := by
          simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp _ (List.getElem_mem hj)]
        rw [ha_same] at ha ⊢; rw [hb_same] at hb ⊢
        exact hpw_old i j hi hj hlt ha hb
  exact hrest mid rfl rfl heff_mid hnt hor

theorem wk_evm_init :
    WorldKeeps WorldOK
      (fun s =>
        [(globN s "evm_empty", if globN s "evm_empty" = 0 then 0 else 8),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "null_address", if globN s "null_address" = 0 then 0 else 24),
         (globN s "transfer_topic", if globN s "transfer_topic" = 0 then 0 else 32),
         (globN s "vm_system_address", if globN s "vm_system_address" = 0 then 0 else 24)])
      ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf",
       "transfer_topic", "vm_system_address"]
      stdKeep NoExtra (ofString "evm_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "evm_init") =
      some ([], sourceFnBody Guest.Software.guestFn_evm_init, .one) :=
    lookup_of_guestAst_getElem 566 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_evm_init) rfl
  refine ⟨_, _, _, hlook, fun {F} s hc hWOK _ hnt hres => ?_⟩
  let Bevm : List (String × Nat) := [("keccak_st", 200), ("keccak_pad", 136)]
  let Rlevm : List Ivl :=
    [(globN s "evm_empty", if globN s "evm_empty" = 0 then 0 else 8),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
     (globN s "null_address", if globN s "null_address" = 0 then 0 else 24),
     (globN s "transfer_topic", if globN s "transfer_topic" = 0 then 0 else 32),
     (globN s "vm_system_address", if globN s "vm_system_address" = 0 then 0 else 24)]
  let gwevm : List String :=
    ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf",
     "transfer_topic", "vm_system_address"]
  refine InitEff.to_worldStep (B := Bevm) hWOK (by decide) (by decide) ?_
  have hhl_he : heapLimit ≤ heapEnd := by decide
  -- Deconstruct `evm_init` body: `decCall "mark" heap_mark [] (decCall "s" alloc [40] inner)`
  let inner0 : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_evm_init with
    | .decCall _ _ _ _ (.decCall _ _ _ _ t) => t
    | _ => .skip
  -- `inner0` has 33 `storeByte`s to `"s"`, followed by `heap_release(mark) ; ...`
  let sbList : List (ProgHOL 64) := match inner0 with
    | .seq b0 (.seq b1 (.seq b2 (.seq b3 (.seq b4 (.seq b5 (.seq b6 (.seq b7 (.seq b8 (.seq b9
      (.seq b10 (.seq b11 (.seq b12 (.seq b13 (.seq b14 (.seq b15 (.seq b16 (.seq b17 (.seq b18 (.seq b19
      (.seq b20 (.seq b21 (.seq b22 (.seq b23 (.seq b24 (.seq b25 (.seq b26 (.seq b27 (.seq b28 (.seq b29
      (.seq b30 (.seq b31 (.seq b32 _)))))))))))))))))))))))))))))))) =>
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
         b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
         b20, b21, b22, b23, b24, b25, b26, b27, b28, b29,
         b30, b31, b32]
    | _ => []
  let fromRelease : ProgHOL 64 :=
    .seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
    (.seq (.call (some (some (.global, ofString "transfer_topic"), none)) (ofString "alloc") [.const 32])
    (.seq (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")])
    (.seq (.call (some (some (.global, ofString "vm_system_address"), none)) (ofString "alloc") [.const 24])
    (.dec (ofString "i") .one (.const 0)
      (.seq (.while (.cmp .less (.var .local (ofString "i")) (.const 20))
          (.seq (.storeByte (.op .add [.var .global (ofString "vm_system_address"), .var .local (ofString "i")]) (.const 255))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (.seq (.storeByte (.op .add [.var .global (ofString "vm_system_address"), .const 19]) (.const 254))
      (.seq (.call (some (some (.global, ofString "null_address"), none)) (ofString "alloc") [.const 24])
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "null_address"), .const 24])
      (.seq (.call (some (some (.global, ofString "evm_empty"), none)) (ofString "alloc") [.const 8])
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "evm_empty"), .const 8])
      (.seq (.call (some (some (.global, ofString "evm_key_buf"), none)) (ofString "alloc") [.const 32])
      (.seq (.call (some (some (.global, ofString "pre_hdr_buf"), none)) (ofString "alloc") [.const 96])
        (.return (.const 0))))))))))))))
  have hbody : sourceFnBody Guest.Software.guestFn_evm_init =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "s") .one (ofString "alloc") [.const 40]
          (seqList sbList fromRelease)) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s Rlevm Bevm gwevm hWOK.1 hc
  -- 1. `decCall "mark" heap_mark []`
  refine initEff_decCall_heap_mark (ofString "mark") heff0 hnt (Or.inr hres)
    (fun mw s1 hmw0 hs1_loc hs1_glob heff1 hnt1 hor1 => ?_)
  have hmw_glob : globN s "heap_ptr" = mw.toNat := by simp [globN, hmw0]
  -- 2. `decCall "s" alloc [40]`
  refine initEff_decCall_alloc_local (ofString "s") 40 heff1 ⟨by omega, by omega⟩ (by decide) hnt1 hor1
    (fun ps qs s2 hps1 _ hps_lo hps_q hq_lim hs2_loc hs2_glob heff2 hnt2 hor2 => ?_)
  have hps_eq_mw : ps = mw := by
    rw [hs1_glob, hmw0] at hps1; injection hps1 with h; injection h with h; injection h with h; exact h.symm
  subst hps_eq_mw
  have hps_lim : ps.toNat + 40 ≤ heapLimit := le_trans hps_q hq_lim
  have hs_loc2 : s2.locals.lookup (ofString "s") = some (.val (.word ps)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hmark_loc2 : s2.locals.lookup (ofString "mark") = some (.val (.word ps)) := by
    rw [hs2_loc, hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show (ofString "s" == ofString "mark") = false by decide]
  -- 3. 33 `storeByte`s to local `"s"`!
  rw [evaluate_seqList_eq] at hnt2 hor2 ⊢
  have hsb_eff := checkByteStoresLocal_sound (ofString "s") 40 (by omega) (seqBlock sbList) rfl
    s2 ps heff2.code heff2.arena.1 hs_loc2
  refine initEff_seq hnt2 hor2
    (fun _ _ => heff2.of_byteEff hsb_eff.1 (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hps_lo, hps_lim⟩)))
    (fun s3 hs3 heff3 hnt3 hor3 => ?_)
  have hs3_glob : s3.globals = s2.globals := by
    have hb := hsb_eff.1; rw [hs3] at hb; exact hb.globals
  have hs3_s : s3.locals.lookup (ofString "s") = some (.val (.word ps)) := by
    have hs := hsb_eff.2; rw [hs3] at hs; exact hs (Or.inl rfl)
  -- Wait: did `seqBlock sbList` touch local `"mark"`? No! `seqBlock sbList` has ONLY `.seq` and `.storeByte`!
  have hs3_loc_eq : s3.locals = s2.locals := by
    let isSb : ProgHOL 64 → Bool := fun
      | .storeByte _ _ => true
      | _ => false
    have hseq_sb_loc : ∀ (psL : List (ProgHOL 64)) (t : PanSemStateFiniteExact 64 F),
        psL.all isSb = true →
        (evaluateHOLFiniteState t (seqBlock psL)).2.locals = t.locals := by
      intro psL t hall
      induction psL generalizing t with
      | nil => simp [seqBlock, evaluateHOLFiniteState_skip]
      | cons hd tl ih =>
        have hhd_ok : isSb hd = true := by rw [List.all_cons, Bool.and_eq_true] at hall; exact hall.1
        have htl_ok : tl.all isSb = true := by rw [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
        cases hd <;> try (simp [isSb] at hhd_ok)
        rename_i d v
        have hhd_loc := (evaluate_storeByte_control_frame t d v).2.2.1
        cases tl with
        | nil => exact hhd_loc
        | cons q qs =>
          change (evaluateHOLFiniteState t (.seq (.storeByte d v) (seqBlock (q :: qs)))).2.locals = t.locals
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hr : evaluateHOLFiniteState t (.storeByte d v) with ⟨r1, m1⟩
          rw [hr] at hhd_loc
          cases r1 with
          | some _ => exact hhd_loc
          | none => exact (ih m1 htl_ok).trans hhd_loc
    have hloc3 := hseq_sb_loc sbList s2 rfl
    rwa [hs3] at hloc3
  have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word ps)) := by
    rw [hs3_loc_eq]; exact hmark_loc2
  -- 4. `heap_release(mark)`! Notice no global buffer was modified yet (`s3.globals` only updated `"heap_ptr"`),
  -- so `globN s3 gn.1 = globN s gn.1` for every `gn ∈ globalBuffers`!
  dsimp only [fromRelease] at hnt3 hor3 ⊢
  refine initEff_seq_heap_release (.var .local (ofString "mark")) ps hWOK.1.2 heff3 (by decide)
    hs3_mark (by rw [hmw_glob]) (by rw [← hmw_glob]; exact hWOK.1.2.2.1)
    (by rw [← hmw_glob]; exact hWOK.1.2.2.2.2.2.2.1)
    (fun gn hgn => by
      left
      have hgb_not_hp : ∀ p ∈ globalBuffers, (ofString "heap_ptr" == ofString p.1) = false := by decide
      simp [hs3_glob, hs2_glob, hs1_glob, globN, HolFiniteMapExact.lookup_update, FUPDATE, hgb_not_hp gn hgn])
    hnt3 hor3
    (fun s4 hs4_loc hs4_glob heff4 hnt4 hor4 => ?_)
  have hs4_s : s4.locals.lookup (ofString "s") = some (.val (.word ps)) := by
    rw [hs4_loc]; exact hs3_s
  -- 5. `transfer_topic := alloc(32)`
  refine initEff_seq_alloc_global "transfer_topic" 32 (.const 32) heff4
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt4 hor4
    (fun s5 ptt hs5_loc _ heff5 hptt5 _ hptt_lo hptt_hi hnt5 hor5 => ?_)
  have htt_lim : ptt.toNat + 32 ≤ heapLimit := le_trans hptt_hi heff5.arena.2.2.1
  have hs5_s : s5.locals.lookup (ofString "s") = some (.val (.word ps)) := by
    rw [hs5_loc]; exact hs4_s
  -- 6. `keccak256(s, 33, transfer_topic)`
  have hkst5 : s5.globals.lookup (ofString "keccak_st") = s.globals.lookup (ofString "keccak_st") :=
    (heff5.gw_kept (ofString "keccak_st") (by decide)).symm
  have hkpad5 : s5.globals.lookup (ofString "keccak_pad") = s.globals.lookup (ofString "keccak_pad") :=
    (heff5.gw_kept (ofString "keccak_pad") (by decide)).symm
  have hb_k : (evaluateHOLFiniteState s5
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")])).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s5
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")])).1 = none ∨
      Resumes (evaluateHOLFiniteState s5
        (.call (some (none, none)) (ofString "keccak256")
          [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")])).1) →
    ByteEff s5 (evaluateHOLFiniteState s5
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")])).2
      [bufferRegion s ("keccak_st", 200), bufferRegion s ("keccak_pad", 136), (ptt.toNat, 32)] := by
    intro hnt_k hor_k
    have hargs : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
        [.var .local (ofString "s"), .const 33, .var .global (ofString "transfer_topic")] =
        some [.val (.word ps), .val (.word 33), .val (.word ptt)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_s, hptt5]
    exact call0_byteEff funByteEff_keccak256 s5 _ _ heff5.code heff5.arena.1
      (fun vs hvs iv hiv _ => by
        rw [hargs] at hvs; injection hvs with hvs; subst hvs
        have hst_eq : globBufIvl s5.globals "keccak_st" 200 = bufferRegion s ("keccak_st", 200) := by
          unfold globBufIvl bufferRegion globMapN globN; dsimp only; rw [hkst5]; rfl
        have hpad_eq : globBufIvl s5.globals "keccak_pad" 136 = bufferRegion s ("keccak_pad", 136) := by
          unfold globBufIvl bufferRegion globMapN globN; dsimp only; rw [hkpad5]; rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, valWordNat, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, hst_eq, hpad_eq] at hiv
        rcases hiv with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩)
      hnt_k hor_k
  refine initEff_seq hnt5 hor5
    (fun hnt_k hor_k => heff5.of_byteEff (hb_k hnt_k hor_k) (fun iv hiv _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨("keccak_st", 200), by simp [Bevm], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by simp [Bevm], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inr ⟨hptt_lo, htt_lim⟩)))
    (fun s6 _ heff6 hnt6 hor6 => ?_)
  -- 7. `vm_system_address := alloc(24)` + `dec "i" 0` + loop `i < 20` + `storeByte (vm_system_address + 19) 254`
  refine initEff_seq_alloc_global "vm_system_address" 24 (.const 24) heff6
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt6 hor6
    (fun s7 pvsa _ _ heff7 hpvsa7 _ hpvsa_lo hpvsa_hi hnt7 hor7 => ?_)
  have hvsa_lim : pvsa.toNat + 24 ≤ heapLimit := le_trans hpvsa_hi heff7.arena.2.2.1
  refine initEff_dec_const (ofString "i") 0 heff7 hnt7 hor7 (fun heff8 hnt8 hor8 => ?_)
  let s8 := setVarHOLFinite (ofString "i") (.val (.word 0)) s7
  have hpvsa8 : s8.globals.lookup (ofString "vm_system_address") = some (.val (.word pvsa)) := hpvsa7
  have hi8 : s8.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hvsa_lp := byteEff_counted_storeByte_loop s8.clock s8 pvsa 0 20 24
    (.op .add [.var .global (ofString "vm_system_address"), .var .local (ofString "i")])
    (.const 255)
    le_rfl heff8.arena.1 (by decide) (le_trans hvsa_lim hhl_he) hi8 (by decide)
    (fun t iv htg hti hlt => by
      have hp_t : t.globals.lookup (ofString "vm_system_address") = some (.val (.word pvsa)) := by
        rw [htg]; exact hpvsa8
      have h20 : (20 : BitVec 64).toNat = 20 := rfl
      rw [h20] at hlt
      have hiv_eq : BitVec.ofNat 64 iv.toNat = iv := BitVec.eq_of_toNat_eq (by simp)
      refine ⟨iv.toNat, by omega, ?_⟩
      simp [evalHOLExact, evalListHOLExact, hp_t, hti, valueIsWord, valueWord, wordOpHOL, wordOp, hiv_eq])
  refine initEff_seq hnt8 hor8
    (fun _ _ => heff8.of_byteEff hvsa_lp (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpvsa_lo, hvsa_lim⟩)))
    (fun s9 hs9 heff9 hnt9 hor9 => ?_)
  have hs9_glob : s9.globals = s8.globals := by
    dsimp only at hvsa_lp; change evaluateHOLFiniteState s8 _ = (none, s9) at hs9
    rw [hs9] at hvsa_lp; exact hvsa_lp.globals
  have hpvsa9 : s9.globals.lookup (ofString "vm_system_address") = some (.val (.word pvsa)) := by
    rw [hs9_glob]; exact hpvsa8
  have hsb_19 : ByteEff s9 (evaluateHOLFiniteState s9
      (.storeByte (.op .add [.var .global (ofString "vm_system_address"), .const 19]) (.const 254))).2
      [(pvsa.toNat, 24)] := by
    refine byteEff_storeByte_at heff9.arena.1 _ _ pvsa 19 24 (le_trans hvsa_lim hhl_he)
      (fun _ => ⟨(pvsa.toNat, 24), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩) (by omega) ?_
    simp [evalHOLExact, evalListHOLExact, hpvsa9, valueIsWord, valueWord, wordOpHOL, wordOp]
  refine initEff_seq hnt9 hor9
    (fun _ _ => heff9.of_byteEff hsb_19 (fun iv hiv _ => by
      simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpvsa_lo, hvsa_lim⟩)))
    (fun s10 _ heff10 hnt10 hor10 => ?_)
  -- 8. `null_address := alloc(24) ; memzero(null_address, 24)`
  refine initEff_seq_alloc_global "null_address" 24 (.const 24) heff10
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt10 hor10
    (fun s11 pna _ _ heff11 hpna11 _ hpna_lo hpna_hi hnt11 hor11 => ?_)
  have hna_lim : pna.toNat + 24 ≤ heapLimit := le_trans hpna_hi heff11.arena.2.2.1
  refine initEff_seq hnt11 hor11
    (fun hnt_m1 hor_m1 => by
      have hargs : evalListHOLFinite s11 (h := fun a => Classical.propDecidable (s11.memaddrs a))
          [.var .global (ofString "null_address"), .const 24] = some [.val (.word pna), .val (.word 24)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpna11]
      have hb := call0_byteEff funByteEff_memzero s11 _ [(pna.toNat, 24)] heff11.code heff11.arena.1
        (fun vs hvs iv hiv _ => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hiv; subst hiv
          exact ⟨(pna.toNat, 24), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        hnt_m1 hor_m1
      exact heff11.of_byteEff hb (fun iv hiv _ => by
        simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpna_lo, hna_lim⟩)))
    (fun s12 _ heff12 hnt12 hor12 => ?_)
  -- 9. `evm_empty := alloc(8) ; memzero(evm_empty, 8)`
  refine initEff_seq_alloc_global "evm_empty" 8 (.const 8) heff12
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt12 hor12
    (fun s13 pee _ _ heff13 hpee13 _ hpee_lo hpee_hi hnt13 hor13 => ?_)
  have hee_lim : pee.toNat + 8 ≤ heapLimit := le_trans hpee_hi heff13.arena.2.2.1
  refine initEff_seq hnt13 hor13
    (fun hnt_m2 hor_m2 => by
      have hargs : evalListHOLFinite s13 (h := fun a => Classical.propDecidable (s13.memaddrs a))
          [.var .global (ofString "evm_empty"), .const 8] = some [.val (.word pee), .val (.word 8)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpee13]
      have hb := call0_byteEff funByteEff_memzero s13 _ [(pee.toNat, 8)] heff13.code heff13.arena.1
        (fun vs hvs iv hiv _ => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hiv; subst hiv
          exact ⟨(pee.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        hnt_m2 hor_m2
      exact heff13.of_byteEff hb (fun iv hiv _ => by
        simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hpee_lo, hee_lim⟩)))
    (fun s14 _ heff14 hnt14 hor14 => ?_)
  -- 10. `evm_key_buf := alloc(32) ; pre_hdr_buf := alloc(96) ; return 0`
  refine initEff_seq_alloc_global "evm_key_buf" 32 (.const 32) heff14
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt14 hor14
    (fun s15 _ _ _ heff15 _ _ _ _ hnt15 hor15 => ?_)
  refine initEff_seq_alloc_global "pre_hdr_buf" 96 (.const 96) heff15
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt15 hor15
    (fun s16 _ _ _ heff16 _ _ _ _ _ _ => initEff_return _ heff16)

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

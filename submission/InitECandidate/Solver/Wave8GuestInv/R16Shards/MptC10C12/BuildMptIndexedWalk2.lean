import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
set_option linter.unusedVariables false
open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let n : Name := Name.str (Name.mkSimple "_private") "InitECandidate"
    |>.str "Solver" |>.str "Wave8GuestInv" |>.str "R16Shards" |>.str "MptC10C12"
    |>.str "MptSetRootKeeps" |>.num 0
    |>.str "InitECandidate" |>.str "Solver" |>.str "Wave8GuestInv"
    |>.str "R16Shards" |>.str "MptC10C12" |>.str "mpt_root_body_eff"
  let some ci := env.constants.find? n | throwError "alias target missing"
  let lvls := ci.levelParams.map (fun (v : Name) => Level.param v)
  let val := Expr.const n lvls
  let ty ← Meta.inferType val
  addDecl (Declaration.thmDecl
    { name := `InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.wkMptRootFineBody
      levelParams := ci.levelParams, type := ty, value := val })
def bmiRootR (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(locN s "out", 32),
   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
def bmiRootB : List (String × Nat) := [("keccak_pad", 136), ("keccak_st", 200)]
theorem bmiRoot_gw_sub :
    ∀ g ∈ coreWorldGlobals, ofString g ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
  intro g hg hmem
  simp only [coreWorldGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  <;> exact absurd hmem (by decide)
theorem callee_locals_three_lookup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (s1 s2 s3 : ShapeHOL)
    {body : ProgHOL 64} {ret : ShapeHOL}
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, ret)) :
    ∃ v1 v2 v3,
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧
      shapeEqHOL s1 (shapeOfHOLExact v1) = true ∧
      shapeEqHOL s2 (shapeOfHOLExact v2) = true ∧
      shapeEqHOL s3 (shapeOfHOLExact v3) = true := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · exact absurd hlook (by simp)
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, hlen, hall⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      rcases values with _ | ⟨v1, values⟩
      · simp at hlen
      rcases values with _ | ⟨v2, values⟩
      · simp at hlen
      rcases values with _ | ⟨v3, values⟩
      · simp at hlen
      simp only [List.zip_cons_cons, List.zip_nil_left, List.all_cons, Bool.and_eq_true,
        Bool.and_true, List.all_nil] at hall
      refine ⟨v1, v2, v3, ?_, ?_, ?_, hall.1, hall.2.1, hall.2.2⟩
      · simp [List.zip, List.zipWith, List.foldl, hnd.1.1, hnd.1.2]
      · simp [List.zip, List.zipWith, List.foldl, hnd.2.1]
      · simp [List.zip, List.zipWith, List.foldl]
    · exact absurd raw (by simp)
theorem bmiWk_word_of_shape {width : Nat} [NeZero width] {v : ValueHOL width}
    (hs : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w, v = .val (.word w) := by
  cases v with
  | val x =>
    cases x with
    | word w => exact ⟨w, rfl⟩
  | rStruct fields => simp [shapeOfHOLExact, shapeEqHOL] at hs
  | nStruct name fields => simp [shapeOfHOLExact, shapeEqHOL] at hs
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem bmiWk_entry_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (values : List (ValueHOL 64))
    (hlook : lookupCodeHOLFinite s.code.lookup
      (ofString "build_mpt_indexed") values =
        some (sourceFnBody Guest.Software.guestFn_build_mpt_indexed, s.locals, .one)) :
    ∃ wa wn wo : BitVec 64,
      s.locals.lookup (ofString "slice_arr") = some (.val (.word wa)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
      s.locals.lookup (ofString "out") = some (.val (.word wo)) := by
  have hl' : s.code.lookup (ofString "build_mpt_indexed") =
      some ([(ofString "slice_arr", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_build_mpt_indexed, .one) := by
    rw [hcode]; exact lookup_build_mpt_indexed_strong
  obtain ⟨v1, v2, v3, h1, h2, h3, hs1, hs2, hs3⟩ :=
    callee_locals_three_lookup s (ofString "build_mpt_indexed")
      (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one
      hl' values s.locals hlook
  obtain ⟨wa, rfl⟩ := bmiWk_word_of_shape hs1
  obtain ⟨wn, rfl⟩ := bmiWk_word_of_shape hs2
  obtain ⟨wo, rfl⟩ := bmiWk_word_of_shape hs3
  exact ⟨wa, wn, wo, h1, h2, h3⟩
theorem globN_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (name : String) :
    globN { s with locals := locals, clock := k } name = globN s name := rfl
theorem locN_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (name : String)
    (h : locals.lookup (ofString name) = s.locals.lookup (ofString name)) :
    locN { s with locals := locals, clock := k } name = locN s name := by
  simp only [locN, h]
theorem globN_update_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (w : BitVec 64) :
    globN { s with globals := s.globals.update (ofString name, .val (.word w)) } name =
      w.toNat := by
  unfold globN HolFiniteMapExact.update FUPDATE
  simp
theorem globN_update_ne {F : Type} (s : PanSemStateFiniteExact 64 F) {base : String}
    (name : String) (hbeq : (ofString base == ofString name) = false) (w : BitVec 64) :
    globN { s with globals := s.globals.update (ofString base, .val (.word w)) } name =
      globN s name := by
  unfold globN HolFiniteMapExact.update FUPDATE
  simp [hbeq]
theorem keccakBufIvls_congr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : globN post "keccak_pad" = globN s "keccak_pad")
    (hgs : globN post "keccak_st" = globN s "keccak_st") :
    keccakBufIvls post = keccakBufIvls s := by
  simp only [keccakBufIvls, bufferRegion, hg, hgs]
theorem worldOwned_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    worldOwned { s with locals := locals, clock := k } S Nd = worldOwned s S Nd := rfl
theorem worldTypedIvls_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    worldTypedIvls { s with locals := locals, clock := k } S Nd = worldTypedIvls s S Nd := rfl
def BmiReadyG (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  BuildMptIndexedReady s ∧ WorldTypedWith s S Nd ∧
  IvlsDisj (bmiWkRti s) (worldTypedIvls s S Nd) ∧
  IvlsDisj [(locN s "slice_arr", 16 * locN s "n")] (worldOwned s S Nd) ∧
  IvlsDisj [(locN s "out", 32)] ((locN s "slice_arr", 16 * locN s "n") :: worldOwned s S Nd) ∧
  Inside (locN s "out", 32) sourceBase (globN s "heap_ptr") ∧
  globN s "mpt_key_scratch" ≠ 0 ∧
  (∀ i, i < locN s "n" → memW s (locN s "slice_arr" + 16 * i) + 8 ≤ globN s "heap_ptr") ∧
  (∀ i, i < locN s "n" → ∀ iv ∈ keccakBufIvls s, 0 < iv.2 →
    ¬ InIvl (memW s (locN s "slice_arr" + 16 * i)) iv)
theorem strong_bmiReadyG {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptIndexedReadyStrong s) : ∃ S Nd, BmiReadyG s S Nd := by
  obtain ⟨S, Nd, h2, h3, h4, h5, h6, h7, h8⟩ := h.2
  exact ⟨S, Nd, h.1, h2, h3, h4, h5, h6, h7, h8⟩
theorem bmiReadyG_locals {F : Type} (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : BmiReadyG s S Nd)
    (hl : ∀ n ∈ (["slice_arr", "n", "out"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    BmiReadyG { s with locals := locals, clock := k } S Nd := by
  obtain ⟨hR, hWT, hdjRti, hdjSlice, hdjOut, hout32, hkey, hhp, hkec⟩ := h
  have hsa : locN { s with locals := locals, clock := k } "slice_arr" = locN s "slice_arr" :=
    locN_locals s locals k "slice_arr" (hl "slice_arr" (by simp))
  have hn : locN { s with locals := locals, clock := k } "n" = locN s "n" :=
    locN_locals s locals k "n" (hl "n" (by simp))
  have hout : locN { s with locals := locals, clock := k } "out" = locN s "out" :=
    locN_locals s locals k "out" (hl "out" (by simp))
  refine ⟨localsOnly_buildMptIndexedReady s locals k hl hR,
    (worldTypedWith_build_locals s locals k S Nd).2 hWT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hRti : bmiWkRti { s with locals := locals, clock := k } = bmiWkRti s := by
      unfold bmiWkRti
      simp only [hout, globN_locals]
      rfl
    rw [hRti, worldTypedIvls_locals]
    exact hdjRti
  · rw [hsa, hn, worldOwned_locals]
    exact hdjSlice
  · rw [hout, hsa, hn, worldOwned_locals]
    exact hdjOut
  · rw [hout, globN_locals]
    exact hout32
  · rw [globN_locals]
    exact hkey
  · rw [hsa, hn, globN_locals]
    exact hhp
  · rw [hsa, hn, keccakBufIvls_congr (globN_locals s locals k "keccak_pad")
      (globN_locals s locals k "keccak_st")]
    exact hkec
theorem bmi2_pairwise_mem {α : Type} {R : α → α → Prop} (l : List α)
    (hR : ∀ a ∈ l, ∀ b ∈ l, R a b) : l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.Pairwise.cons ?_ (ih fun b hb c hc =>
      hR b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc))
    exact fun b hb => hR a (List.mem_cons_self) b (List.mem_cons_of_mem a hb)
theorem bmi2_flatMap_congr {α β : Type} (l : List α) {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih fun b hb => h b (List.mem_cons_of_mem a hb)]
theorem bmi2_beq_ne_heap_names : ∀ name ∈ (["scratch_ptr", "journal", "journal_cap", "ws", "bs",
    "ts", "bo", "bal_accounts", "bal_idx_accts", "bal_idx_stor", "journal_n", "keccak_pad",
    "keccak_st", "mpt_hash_scratch", "mpt_key_scratch", "out"] : List String),
    (ofString "heap_ptr" == ofString name) = false := by decide
theorem bmi2_gbuf_ne_heap : ∀ gn ∈ globalBuffers, (ofString "heap_ptr" == ofString gn.1) = false :=
  by decide
theorem bmi2_tr_ne_heap : ∀ gn ∈ typedRecords, (ofString "heap_ptr" == ofString gn.1) = false :=
  by decide
theorem bmi2_core_beq_ne_heap : ∀ g ∈ coreWorldGlobals,
    (ofString "heap_ptr" == ofString g) = false := by
  intro g hg
  simp only [coreWorldGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bmi2_beq_ne_heap_names _ (by decide)
theorem bmi2_buf4_ne_heap : ∀ gn ∈ [("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
    ("keccak_pad", 136), ("keccak_st", 200)], (ofString "heap_ptr" == ofString gn.1) = false :=
  by decide
theorem bmi2_align64 {b : Nat} (hb : b < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
  unfold panByteAlignHOL
  simp
  omega
set_option maxHeartbeats 4000000 in
theorem bmiReadyG_mpt_new {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (q : BitVec 64) (h : BmiReadyG s S Nd)
    (hARs : ArenaReady s) (hARp : ArenaReady post) (hbe : post.be = s.be)
    (hglob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hmem : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      a.toNat = globN s "heap_ptr" ∨ a.toNat = globN s "heap_ptr" + 8)
    (hag : AllocatorGrows s post) (hq_lim : q.toNat ≤ heapLimit)
    (hmono : globN s "heap_ptr" + 16 ≤ q.toNat)
    (hloc : ∀ n ∈ (["slice_arr", "n", "out"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    BmiReadyG post S Nd ∧
      worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
      worldOwned post S Nd = worldOwned s S Nd ∧
      nodeExtents post Nd = nodeExtents s Nd := by
  obtain ⟨hR, hWT, hdjRti, hdjSlice, hdjOut, hout32, hkey, hhp, hkec⟩ := h
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hin_s, hin_e⟩ := hR.2.2.2.1
  obtain ⟨hsb, hhl, hss_fmp, hfmp_sp, hsp_se, hhp8, hfmp8, hsp8, hGW⟩ := hARs.2
  obtain ⟨hsb_p, hhl_p, hss_fmp_p, hfmp_sp_p, hsp_se_p, hhp8_p, hfmp8_p, hsp8_p, hGW_p⟩ := hARp.2
  have hAOKs : ArenaOK s := ⟨hsb, hhl, hss_fmp, hfmp_sp, hsp_se, hhp8, hfmp8, hsp8, hGW⟩
  have hAOKp : ArenaOK post :=
    ⟨hsb_p, hhl_p, hss_fmp_p, hfmp_sp_p, hsp_se_p, hhp8_p, hfmp8_p, hsp8_p, hGW_p⟩
  have hsb_val : sourceBase = 2701131776 := Fast_C08WkShard03.sourceBase_val
  have hlim_eq : heapLimit = scratchStart := rfl
  have hlim64 : heapLimit < 2 ^ 64 := by rw [Fast_C08WkShard03.heapLimit_val]; decide
  have hgap : globN s "heap_ptr" + 16 ≤ scratchStart := by
    rw [Fast_C08WkShard03.scratchStart_val]
    have h2 : q.toNat ≤ 2952790016 := by
      have h3 := hq_lim
      rw [Fast_C08WkShard03.heapLimit_val] at h3
      exact h3
    omega
  have hglobN : ∀ name : String,
      globN post name =
        globN { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) } name := by
    intro name
    rw [show globN post name = globN { s with globals := post.globals } name from rfl, hglob]
  have hg_ne : ∀ name : String, (ofString "heap_ptr" == ofString name) = false →
      globN post name = globN s name := by
    intro name hbeq
    rw [hglobN name]
    exact globN_update_ne s name hbeq q
  have hg_hp : globN post "heap_ptr" = q.toNat := by
    rw [hglobN "heap_ptr"]
    exact globN_update_eq s "heap_ptr" q
  have hg10 : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg =>
    hg_ne g (bmi2_core_beq_ne_heap g hg)
  have hlocN : ∀ n ∈ (["slice_arr", "n", "out"] : List String), locN post n = locN s n := by
    intro n hn
    simp only [locN, hloc n hn]
  have hdisj_fresh : ∀ i : Ivl, i.2 = 0 ∨ Allocated s i →
      i.2 = 0 ∨ globN s "heap_ptr" + 16 ≤ i.1 ∨ i.1 + i.2 ≤ globN s "heap_ptr" := by
    intro i hj
    have hinside : Inside (globN s "heap_ptr", 16) (globN s "heap_ptr") (globN post "heap_ptr") :=
      ⟨le_refl _, hmono.trans (le_of_eq hg_hp.symm)⟩
    have hdj := disj_fresh_heap_allocated hAOKs hAOKp hinside hj
    rcases hdj with h0 | h0 | hd1 | hd2
    · exact absurd h0 (by simp)
    · exact Or.inl h0
    · exact Or.inr (Or.inl hd1)
    · exact Or.inr (Or.inr hd2)
  have hmem_cell : ∀ c : Nat, c < 2 ^ 64 → c ≠ globN s "heap_ptr" →
      c ≠ globN s "heap_ptr" + 8 →
      post.memory (BitVec.ofNat 64 c) = s.memory (BitVec.ofNat 64 c) := by
    intro c hc h1 h2
    have hbit : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
    by_contra hne
    rcases hmem (BitVec.ofNat 64 c) hne with h | h <;> omega
  have hmemW : ∀ c : Nat, c < 2 ^ 64 → c ≠ globN s "heap_ptr" →
      c ≠ globN s "heap_ptr" + 8 → memW post c = memW s c := by
    intro c hc h1 h2
    simp only [memW, hmem_cell c hc h1 h2]
  have htr_alloc : ∀ r ∈ typedRecords, globN s r.1 ≠ 0 → Allocated s (globN s r.1, r.2) := by
    intro r hr hnz
    have hmemw : (globN s r.1, if globN s r.1 = 0 then 0 else r.2) ∈ worldTypedIvls s S Nd :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨r, hr, rfl⟩))))))))))
    rcases M13.worldTypedIvls_allocated ⟨hT, hJ, hF, hTr⟩ hmemw with h0 | hal
    · simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [if_neg hnz] at h0
      rcases hr with rfl | rfl | rfl | rfl <;> omega
    · rw [if_neg hnz] at hal
      exact hal
  have hjr_alloc : globN s "journal_cap" ≠ 0 →
      Allocated s (globN s "journal", 32 * globN s "journal_cap") := by
    intro hnz
    have hmemw : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap") ∈ worldTypedIvls s S Nd :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))))))))
    rcases M13.worldTypedIvls_allocated ⟨hT, hJ, hF, hTr⟩ hmemw with h0 | hal
    · exact absurd h0 (by omega)
    · rw [if_neg hnz] at hal
      exact hal
  have hbyte_eq : ∀ b : Nat, b < 2 ^ 64 →
      (∃ i ∈ worldTypedIvls s S Nd, i.1 ≤ b ∧ b < i.1 + i.2) → memB post b = memB s b := by
    intro b hb64 ⟨i, hi, hi1, hi2⟩
    have hcal : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := bmi2_align64 hb64
    have hdisj := hdisj_fresh i (M13.worldTypedIvls_allocated ⟨hT, hJ, hF, hTr⟩ hi)
    have hcal_ne : b / 8 * 8 ≠ globN s "heap_ptr" ∧ b / 8 * 8 ≠ globN s "heap_ptr" + 8 := by
      rcases hdisj with h0 | hd1 | hd2 <;> (constructor <;> omega)
    have hcellB : post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) =
        s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
      by_contra hne
      rcases hmem (panByteAlignHOL (BitVec.ofNat 64 b)) hne with h | h <;> omega
    simp only [memB, hcellB, hbe]
  have hunhit : ∀ i : Ivl, Allocated s i → IvlUnhit s post i := by
    intro i hal a ha8 hhits
    obtain ⟨hh1, hh2⟩ := hhits
    by_contra hne
    rcases hmem a hne with h | h <;>
      rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> omega
  have hbo_eq : blockOutObjects post = blockOutObjects s :=
    (blockOutObjects_eq_of_bo_unhit hAOKs hF
      (hg_ne "bo" (bmi2_beq_ne_heap_names "bo" (by simp))) hT.2.2.2.2.2.2.2.2.2.2.1
      (fun hbo => by
        have hmemw : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
            worldTypedIvls s S Nd :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
            (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨("bo", 88), by simp [typedRecords],
              by simp only [hbo]⟩))))))))))
        rcases M13.worldTypedIvls_allocated ⟨hT, hJ, hF, hTr⟩ hmemw with h0 | hal
        · rw [if_neg hbo] at h0; exact absurd h0 (by omega)
        · rw [if_neg hbo] at hal; exact hunhit _ hal)
      (fun i hi hi24 => hunhit i (by
        have hfix : i ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))
        rcases hF.1 i hfix with h0 | ⟨hal, _⟩
        · rw [hi24] at h0; exact absurd h0 (by omega)
        · exact hal))).1
  have hbal_eq : balObjects post = balObjects s :=
    (balObjects_eq_of_unhit hAOKs hT hF
      (hg_ne "bal_accounts" (bmi2_beq_ne_heap_names "bal_accounts" (by simp)))
      (fun t ht i hi => hunhit i ((hT.2.1 t ht).2 i hi).1)
      (fun i hi hi2 => hunhit i (by
        have hfix : i ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append.2 (Or.inr hi)
        rcases hF.1 i hfix with h0 | ⟨hal, _⟩
        · exact absurd h0 hi2
        · exact hal))
      (⟨hmemW 8 (by decide) (by omega) (by omega),
        hmemW 16 (by decide) (by omega) (by omega)⟩)).1
  have hbufOK : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl (hg_ne gn.1 (bmi2_gbuf_ne_heap gn hgn)), ?_⟩
    exact bmi2_pairwise_mem globalBuffers
      (fun a ha b _ hPa _ => absurd (hg_ne a.1 (bmi2_gbuf_ne_heap a ha)) hPa.1)
  obtain ⟨hFp, hbuf2⟩ := fixedTyped_of_freshBufsOK hARs hARp hag hF
    (hg_ne "journal" (bmi2_beq_ne_heap_names "journal" (by simp)))
    (hg_ne "journal_cap" (bmi2_beq_ne_heap_names "journal_cap" (by simp))) hbo_eq hbal_eq hbufOK
  have hgb_map : (globalBuffers.map fun gn =>
      (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.map_congr_left
      (fun gn hgn => by rw [hg_ne gn.1 (bmi2_gbuf_ne_heap gn hgn)])
  have hj_pair : (if globN post "journal_cap" = 0 then 0 else globN post "journal",
      32 * globN post "journal_cap") =
      (if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap") := by
    simp only [hg_ne "journal_cap" (bmi2_beq_ne_heap_names "journal_cap" (by simp)),
      hg_ne "journal" (bmi2_beq_ne_heap_names "journal" (by simp))]
  have htr_map : typedRecords.map
      (fun r => (globN post r.1, if globN post r.1 = 0 then 0 else r.2)) =
      typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) :=
    List.map_congr_left (fun r hr => by
      have h1 := hg_ne r.1 (bmi2_tr_ne_heap r hr)
      simp only [h1])
  have hbuf4 : [("mpt_hash_scratch", 40), ("mpt_key_scratch", 16), ("keccak_pad", 136),
      ("keccak_st", 200)].map (bufferRegion post) =
      [("mpt_hash_scratch", 40), ("mpt_key_scratch", 16), ("keccak_pad", 136),
        ("keccak_st", 200)].map (bufferRegion s) :=
    List.map_congr_left (fun gn hgn => by
      unfold bufferRegion
      rw [hg_ne gn.1 (bmi2_buf4_ne_heap gn hgn)])
  have hfixed_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hgb_map, hj_pair, hbo_eq, hbal_eq]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i :=
    fun t ht i hi => hunhit i ((hT.2.1 t ht).2 i hi).1
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) :=
    fun hnz => hunhit _ (htr_alloc ("ws", 40) (by simp [typedRecords]) hnz)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) :=
    fun hnz => hunhit _ (htr_alloc ("bs", 80) (by simp [typedRecords]) hnz)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) :=
    fun hnz => hunhit _ (htr_alloc ("ts", 72) (by simp [typedRecords]) hnz)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) :=
    fun hnz => hunhit _ (htr_alloc ("bo", 88) (by simp [typedRecords]) hnz)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") :=
    fun hnz => hunhit _ (hjr_alloc hnz)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi hi24 => by
    have hfix : i ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))
    rcases hF.1 i hfix with h0 | ⟨hal, _⟩
    · rw [hi24] at h0; exact absurd h0 (by omega)
    · exact hunhit i hal
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hi2 => by
    have hfix : i ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.2 (Or.inr hi)
    rcases hF.1 i hfix with h0 | ⟨hal, _⟩
    · exact absurd h0 hi2
    · exact hunhit i hal
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) :=
    fun n hn => hunhit _ ((hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 h40 k hk
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, ⟨_, hins2⟩, _⟩
    · exact absurd h0 h40
    · have hnp : nodePath s n = (memW s (n + 32), memW s (n + 40)) := if_pos ⟨h12, h40⟩
      have hmem_np : nodePath s n ∈ nodeExtents s Nd := by
        simp only [nodeExtents, List.mem_flatMap]
        exact ⟨n, hn, by simp⟩
      rw [hnp] at hmem_np
      have hmem_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd :=
        List.mem_append.2 (Or.inr hmem_np)
      exact hbyte_eq _ (by omega) ⟨_, hmem_wti, by omega, by omega⟩
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨hmemW 8 (by decide) (by omega) (by omega), hmemW 16 (by decide) (by omega) (by omega)⟩
  obtain ⟨hWTp, _hOG, hne_eq, hfp_eq⟩ :=
    worldTypedWith_congr_w1 hARs hARp hag hg10 ⟨hT, hJ, hF, hTr⟩
      hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
      hlow hFp hbuf2
  have hwti_eq : worldTypedIvls post S Nd = worldTypedIvls s S Nd := by
    unfold worldTypedIvls
    rw [bmi2_flatMap_congr S hfp_eq, htr_map, hj_pair, hbo_eq, hbal_eq, hne_eq]
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [bmi2_flatMap_congr S hfp_eq, hfixed_eq, hne_eq]
  have hRti : bmiWkRti post = bmiWkRti s := by
    unfold bmiWkRti
    rw [hlocN "out" (by simp),
      hg_ne "keccak_pad" (bmi2_beq_ne_heap_names "keccak_pad" (by simp)),
      hg_ne "keccak_st" (bmi2_beq_ne_heap_names "keccak_st" (by simp)),
      hg_ne "mpt_hash_scratch" (bmi2_beq_ne_heap_names "mpt_hash_scratch" (by simp)),
      hg_ne "mpt_key_scratch" (bmi2_beq_ne_heap_names "mpt_key_scratch" (by simp))]
  have hBR : BuildMptIndexedReady post := by
    refine ⟨⟨hARp, S, (worldTyped_iff_with post S).2 ⟨Nd, hWTp⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro name hname
      obtain ⟨w, hw⟩ := hR.2.1 name hname
      exact ⟨w, (hloc name hname).trans hw⟩
    · rw [hlocN "n" (by simp)]
      exact hR.2.2.1
    · rw [hlocN "slice_arr" (by simp), hlocN "n" (by simp), hg_hp]
      exact ⟨hin_s, by omega⟩
    · rw [hlocN "slice_arr" (by simp), hlocN "n" (by simp)]
      refine ⟨hR.2.2.2.2.1.1, hR.2.2.2.2.1.2.1, ?_⟩
      intro k hk
      have hcell_lt : locN s "slice_arr" + 8 * k < globN s "heap_ptr" := by omega
      have hmad : ordinaryDomain (BitVec.ofNat 64 (locN s "slice_arr" + 8 * k)) := by
        rw [← hARs.1.memaddrs]
        obtain ⟨w, hmad, hmemw⟩ := hR.2.2.2.2.1.2.2 k hk
        exact hmad
      obtain ⟨w, hmad0, hmemw⟩ := hR.2.2.2.2.1.2.2 k hk
      have hcellW : post.memory (BitVec.ofNat 64 (locN s "slice_arr" + 8 * k)) =
          s.memory (BitVec.ofNat 64 (locN s "slice_arr" + 8 * k)) :=
        hmem_cell _ (by omega) (by omega) (by omega)
      exact ⟨w, by rw [hARp.1.memaddrs]; exact hmad,
        by rw [hcellW]; exact hmemw⟩
    · rw [hlocN "slice_arr" (by simp), hlocN "n" (by simp), hbuf4]
      exact hR.2.2.2.2.2.1
    · intro i hi
      rw [hlocN "n" (by simp)] at hi
      rw [hlocN "slice_arr" (by simp)]
      rw [hmemW _ (by omega) (by omega) (by omega)]
      exact hR.2.2.2.2.2.2 i hi
  refine ⟨⟨hBR, hWTp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hwti_eq, hwo_eq, hne_eq⟩
  · rw [hRti, hwti_eq]; exact hdjRti
  · rw [hlocN "slice_arr" (by simp), hlocN "n" (by simp), hwo_eq]
    exact hdjSlice
  · rw [hlocN "out" (by simp), hlocN "slice_arr" (by simp), hlocN "n" (by simp), hwo_eq]
    exact hdjOut
  · rw [hlocN "out" (by simp), hg_hp]
    obtain ⟨h1, h2⟩ := hout32
    exact ⟨h1, h2.trans (le_trans (Nat.le_add_right _ _) hmono)⟩
  · rw [hg_ne "mpt_key_scratch" (bmi2_beq_ne_heap_names "mpt_key_scratch" (by simp))]
    exact hkey
  · intro i hi
    rw [hlocN "n" (by simp)] at hi
    rw [hlocN "slice_arr" (by simp), hg_hp, hmemW _ (by omega) (by omega) (by omega)]
    exact le_trans (hhp i hi) (le_trans (Nat.le_add_right _ _) hmono)
  · intro i hi iv hiv hiv2
    rw [hlocN "n" (by simp)] at hi
    rw [hlocN "slice_arr" (by simp)]
    rw [keccakBufIvls_congr (hg_ne "keccak_pad" (bmi2_beq_ne_heap_names "keccak_pad" (by simp)))
      (hg_ne "keccak_st" (bmi2_beq_ne_heap_names "keccak_st" (by simp)))] at hiv
    rw [hmemW _ (by omega) (by omega) (by omega)]
    exact hkec i hi iv hiv hiv2
theorem bmi2_upd_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (m : MlS)
    (v : ValueHOL 64) (nm : String) (hne : ofString nm ≠ m) :
    (s.locals.update (m, v)).lookup (ofString nm) = s.locals.lookup (ofString nm) := by
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
theorem localsOnly_bmiReadyG :
    LocalsOnly ["slice_arr", "n", "out"] (fun s => ∃ S Nd, BmiReadyG s S Nd) := by
  intro F s locals k hl hs
  obtain ⟨S, Nd, h⟩ := hs
  exact ⟨S, Nd, bmiReadyG_locals s locals k h hl⟩
def BmiAfterMarkC (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ S Nd, BmiReadyG s S Nd ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "mark") = some (.val (.word w))) ∧
    locN s "mark" = globN s "heap_ptr"
theorem decCallResume_heap_mark_bmi2
    (hro : ReadOnlyFn (ofString "heap_mark")) :
    DecCallResumeOn (fun s => ∃ S Nd, BmiReadyG s S Nd) BmiAfterMarkC
      (ofString "mark") (ofString "heap_mark") [] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨S, Nd, hreadyS⟩ := hP
  have hready := ReadOnlyFn.resumeOn localsOnly_bmiReadyG
      (fun s hs => by obtain ⟨S', Nd', h⟩ := hs; exact h.1.1.1.1) hro (ofString "mark")
      (by decide) [] state values body callee ret value post hcode ⟨S, Nd, hreadyS⟩ hargs
      hl hrun
  obtain ⟨S2, Nd2, hready2⟩ := hready
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "heap_mark")
    [] (sourceFnBody Guest.Software.guestFn_heap_mark) body .one ret values callee
    (by rw [hcode]; exact lookup_heap_mark_bmi) hl
  subst hsame
  have hpos : 0 < globN state "heap_ptr" := by
    have hsb := hreadyS.1.1.1.2.1
    have : 0 < sourceBase := by decide
    omega
  obtain ⟨hw, hgw, hwnat⟩ : ∃ hw : BitVec 64,
      state.globals.lookup (ofString "heap_ptr") = some (.val (.word hw)) ∧
      hw.toNat = globN state "heap_ptr" := by
    unfold globN at hpos ⊢
    split at hpos
    · rename_i w hlook; exact ⟨w, hlook, rfl⟩
    · omega
  have hbhm : sourceFnBody Guest.Software.guestFn_heap_mark =
      .return (.var .global (ofString "heap_ptr")) := rfl
  rw [hbhm, evaluateHOLFiniteState_return] at hrun
  have hge : (callEntryStateHOLFinite state callee).globals.lookup (ofString "heap_ptr") =
      some (.val (.word hw)) := hgw
  simp [evalHOLExact, hge, shapeOfHOLExact] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  let resumed := setVarHOLFinite (ofString "mark") (.val (.word hw))
    { emptyLocalsHOLFinite (callEntryStateHOLFinite state callee) with locals := state.locals }
  have hlk : resumed.locals.lookup (ofString "mark") = some (.val (.word hw)) := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hmark : locN resumed "mark" = globN state "heap_ptr" := by
    unfold locN
    rw [hlk]
    exact hwnat
  have hhp : globN resumed "heap_ptr" = globN state "heap_ptr" := rfl
  refine ⟨S2, Nd2, ?_, ⟨hw, by simp [setVarHOLFinite,
    HolFiniteMapExact.lookup_update, FUPDATE]⟩, hmark⟩
  exact hready2
def BmiWkInvE (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ s0 S0 Nd0, BmiWkInv s0 S0 Nd0 (locN s0 "mark") t
private theorem bmi2_bufferRegion_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gs : String × Nat) (hgb : gs ∈ globalBuffers) :
    bufferRegion s gs ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.2 ⟨gs, hgb, rfl⟩
private theorem bmi2_own_zero_or_inside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (h : BmiReadyG s S Nd) :
    ∀ o ∈ worldOwned s S Nd, o = (0, 0) ∨ Inside o sourceBase (globN s "heap_ptr") ∨
      Inside o (globN s "scratch_ptr") scratchEnd :=
  bmiWk_worldOwned_zero_or_inside h.2.1
private theorem bmi2_rti_zero_or_allocated {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (h : BmiReadyG s S Nd) :
    ∀ iv ∈ bmiWkRti s, iv.2 = 0 ∨ Allocated s iv := by
  intro iv hiv
  have hF := h.2.1.2.2.1
  have hgb_al : ∀ gs : String × Nat, gs ∈ globalBuffers →
      (bufferRegion s gs).2 = 0 ∨ Allocated s (bufferRegion s gs) := by
    intro gs hgs
    rcases hF.1 _ (bmi2_bufferRegion_in_fixedObjects s gs hgs) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  simp only [bmiWkRti, List.mem_cons, List.not_mem_nil, or_false] at hiv
  rcases hiv with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl h.2.2.2.2.2.1)
  · exact hgb_al ("keccak_pad", 136) (by decide)
  · exact hgb_al ("keccak_st", 200) (by decide)
  · exact hgb_al ("mpt_hash_scratch", 40) (by decide)
  · exact hgb_al ("mpt_key_scratch", 16) (by decide)
private theorem bmi2_slice_disj_rti {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (h : BmiReadyG s S Nd) :
    IvlsDisj [(locN s "slice_arr", 16 * locN s "n")] (bmiWkRti s) := by
  intro o ho j hj
  simp only [List.mem_singleton] at ho
  subst o
  have hbuf := h.1.2.2.2.2.2.1
  simp only [bmiWkRti, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact Disj.flip (h.2.2.2.2.1 _ (by simp) _ (List.mem_cons_self))
  · exact hbuf _ (by simp) (bufferRegion s ("keccak_pad", 136))
      (List.mem_map.2 ⟨("keccak_pad", 136), by simp, rfl⟩)
  · exact hbuf _ (by simp) (bufferRegion s ("keccak_st", 200))
      (List.mem_map.2 ⟨("keccak_st", 200), by simp, rfl⟩)
  · exact hbuf _ (by simp) (bufferRegion s ("mpt_hash_scratch", 40))
      (List.mem_map.2 ⟨("mpt_hash_scratch", 40), by simp, rfl⟩)
  · exact hbuf _ (by simp) (bufferRegion s ("mpt_key_scratch", 16))
      (List.mem_map.2 ⟨("mpt_key_scratch", 16), by simp, rfl⟩)
theorem decCallResume_mpt_new_bmi2w
    (hwk : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new"))
    (hrt : Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new")) :
    DecCallResumeOn BmiAfterMarkC BmiWkInvE (ofString "m")
      (ofString "mpt_new") [.const 0, .const 0] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨S0, Nd0, hreadyS, hw_mark, hmark_eq⟩ := hP
  let entry := callEntryStateHOLFinite state callee
  have hentryW : WorldOK entry :=
    localsFree_worldOK state callee (state.clock - 1) hreadyS.1.1
  have hstep0 : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) entry (some (.returned value)) post := by
    have hspec := FunSpec.at_lookup hwk state hcode values body callee ret hl hentryW
      (by rw [hrun]; simp)
    rw [hrun] at hspec
    exact hspec (Or.inl ⟨value, rfl⟩)
  have hret0 := FunSpec.at_lookup hrt state hcode values body callee ret hl hentryW.1
    (by rw [hrun]; simp)
  rw [hrun] at hret0
  obtain ⟨wm, rfl, hA_post, hAG, hf0, hroot0, _⟩ := hret0 value rfl
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp state (ofString "mpt_new")
      (ofString "root_node") (ofString "secured") .one .one _ _
      (by rw [hcode]; exact lookup_mpt_new_bmi) _ _ values body callee ret hargs hl
  have hv1 : v1 = .val (.word 0) := by
    simpa [evalAt, evalHOLExact] using he1.symm
  have hv2 : v2 = .val (.word 0) := by
    simpa [evalAt, evalHOLExact] using he2.symm
  subst hv1 hv2
  have hrn0 : locN entry "root_node" = 0 := by
    simp [entry, callEntryStateHOLFinite, locN, hc1]
  have hroot : memW post wm.toNat = 0 := hroot0.trans hrn0
  have hf : FreshBlock state post wm.toNat 16 := hf0
  have hstep : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) state
      (some (.returned (.val (.word wm)))) post := by
    refine ⟨hstep0.1, hstep0.2.1, hstep0.2.2.1, hstep0.2.2.2.1, ?_⟩
    intro S Nd hWT hD
    have hWT_e : WorldTypedWith entry S Nd :=
      (worldTypedWith_build_locals state callee (state.clock - 1) S Nd).2 hWT
    exact hstep0.2.2.2.2 S Nd hWT_e (fun i hi => by simp at hi)
  let postCaller : PanSemStateFiniteExact 64 F := { post with locals := state.locals }
  have hstep_c : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) state
      (some (.returned (.val (.word wm)))) postCaller := by
    refine ⟨localsFree_arenaReady post state.locals post.clock hstep.1,
      hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, ?_⟩
    intro S Nd hWT hD
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hRA⟩ := hstep.2.2.2.2 S Nd hWT hD
    refine ⟨S', Nd', hsub,
      (worldTypedWith_build_locals post state.locals post.clock S' Nd').2 hWT',
      hOG, hFO, hRA⟩
  have hf_c : FreshBlock state postCaller wm.toNat 16 :=
    ⟨hf.1, hf.2.1, hf.2.2⟩
  have hARs : ArenaReady state := hreadyS.1.1.1
  have hWTs : WorldTypedWith state S0 Nd0 := hreadyS.2.1
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hRA⟩ :=
    hstep_c.2.2.2.2 S0 Nd0 hWTs (fun i hi => by simp at hi)
  obtain ⟨wm', hwv, hd0⟩ := hRA (.val (.word wm)) rfl
  let resumed := setVarHOLFinite (ofString "m") (.val (.word wm)) postCaller
  have hARp : ArenaReady resumed := localsFree_arenaReady post
    (state.locals.update (ofString "m", .val (.word wm))) post.clock hstep.1
  have hlk_ne : ∀ n : String, (ofString "m" == ofString n) = false →
      resumed.locals.lookup (ofString n) = state.locals.lookup (ofString n) := by
    intro n hbeq
    have h1 : resumed.locals = state.locals.update (ofString "m", .val (.word wm)) := rfl
    rw [h1, bmi2_upd_lookup_ne state (ofString "m") (.val (.word wm)) n
      (Ne.symm (by simpa using hbeq))]
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "mpt_new")
    [(ofString "root_node", .one), (ofString "secured", .one)]
    (sourceFnBody Guest.Software.guestFn_mpt_new) body .one ret values callee
    (by rw [hcode]; exact lookup_mpt_new_bmi) hl
  subst hsame
  obtain ⟨hp, q, hlk, hhp_eq, hhp_al, hq_eq, hq_hi, hq_al, hg_mid, hm_mid, hbe_mid,
    hAR_mid, hAG_mid, hfr_mid, hw0m, hw8m⟩ :=
    R13Shards.mpt_new_resumes_props entry 0 0 hcode hentryW.1 hc1 hc2
      (by rw [hrun]; exact Or.inl ⟨.val (.word wm), rfl⟩)
  dsimp only [entry] at hlk hhp_eq hg_mid hm_mid hbe_mid
  rw [hrun] at hlk hg_mid hm_mid hbe_mid
  dsimp only at hlk hg_mid hm_mid hbe_mid
  simp at hlk
  subst hlk
  have hhp_st : wm.toNat = globN state "heap_ptr" := by
    simpa [callEntryStateHOLFinite, globN] using hhp_eq
  have hwm_mark : wm.toNat = locN state "mark" := by
    rw [hhp_st, hmark_eq]
  have hglob : post.globals = state.globals.update (ofString "heap_ptr", .val (.word q)) := by
    rw [hg_mid]
    simp [callEntryStateHOLFinite]
  have hmono : globN state "heap_ptr" + 16 ≤ q.toNat := by
    have h1 := hq_eq
    rw [hhp_st] at h1
    omega
  have hmk : globN state "heap_ptr" = locN state "mark" := hmark_eq.symm
  have hglobN : ∀ name : String,
      globN postCaller name =
        globN { state with globals := state.globals.update (ofString "heap_ptr", .val (.word q)) } name := by
    intro name
    rw [show globN postCaller name = globN { state with globals := post.globals } name from rfl, hglob]
  have hg_ne : ∀ name : String, (ofString "heap_ptr" == ofString name) = false →
      globN postCaller name = globN state name := by
    intro name hbeq
    rw [hglobN name]
    exact globN_update_ne state name hbeq q
  have hg_hp : globN postCaller "heap_ptr" = q.toNat := by
    rw [hglobN "heap_ptr"]
    exact globN_update_eq state "heap_ptr" q
  refine ⟨state, S0, Nd0, ?_⟩
  have hreadyS0 : BmiReadyG state S0 Nd0 := hreadyS
  obtain ⟨hR, hWTs2, hdjRti, hdjSlice, hdjOut, hout32, hkey, hhp, hkec⟩ := hreadyS
  obtain ⟨ws, hws⟩ := hR.2.1 "slice_arr" (by simp)
  have hlocNe : ∀ n : String, (ofString "m" == ofString n) = false →
      locN postCaller n = locN state n := by
    intro n hbeq
    rfl
  have hn_r : locN resumed "n" = locN state "n" :=
    locN_setVar_ne postCaller "n" (ofString "m") (.val (.word wm)) (by decide)
  have hsa_r : locN resumed "slice_arr" = locN state "slice_arr" :=
    locN_setVar_ne postCaller "slice_arr" (ofString "m") (.val (.word wm)) (by decide)
  have hout_r : locN resumed "out" = locN state "out" :=
    locN_setVar_ne postCaller "out" (ofString "m") (.val (.word wm)) (by decide)
  have hmark_r : locN resumed "mark" = locN state "mark" :=
    locN_setVar_ne postCaller "mark" (ofString "m") (.val (.word wm)) (by decide)
  have hm_r : locN resumed "m" = wm.toNat := by
    simp [resumed, setVarHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hgn_r : ∀ name : String, globN resumed name = globN postCaller name := fun _ => rfl
  have hg_hp_r : globN resumed "heap_ptr" = q.toNat := by
    rw [hgn_r "heap_ptr"]; exact hg_hp
  have hg_ne_r : ∀ name : String, (ofString "heap_ptr" == ofString name) = false →
      globN resumed name = globN state name := by
    intro name hbeq
    rw [hgn_r name]; exact hg_ne name hbeq
  have hle6 : locN state "mark" ≤ globN resumed "heap_ptr" := by
    rw [hg_hp_r]; have h1 := hmono; have h2 := hmark_eq; omega
  have hle7 : globN resumed "heap_ptr" ≤ heapLimit := by
    rw [hg_hp_r]; exact hq_hi
  have hhp0_eq : wm + 0 = wm := BitVec.add_zero wm
  have hp8_nat : (wm + 8#64).toNat = wm.toNat + 8 :=
    BitVec.toNat_add_of_lt
      (by rw [Fast_C08WkShard03.heapLimit_val] at hq_hi; change wm.toNat + 8 < 2 ^ 64; omega)
  have hm_post : post.memory =
      Wave8Contracts.M26.updW (Wave8Contracts.M26.updW state.memory wm 0) (wm + 8#64) 0 := by
    rw [hm_mid, hhp0_eq]; rfl
  have hmem_lt_hp : ∀ c : Nat, c < globN state "heap_ptr" →
      resumed.memory (BitVec.ofNat 64 c) = state.memory (BitVec.ofNat 64 c) := by
    intro c hc
    have hhl64 : heapLimit < 2 ^ 64 := by rw [Fast_C08WkShard03.heapLimit_val]; decide
    have hc64 : c < 2 ^ 64 := by have := hARs.2.2.1; omega
    have htn : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat]; omega
    have hne0 : BitVec.ofNat 64 c ≠ wm := by
      intro heq; have := congrArg BitVec.toNat heq; omega
    have hne8 : BitVec.ofNat 64 c ≠ wm + 8#64 := by
      intro heq; have := congrArg BitVec.toNat heq; omega
    change post.memory (BitVec.ofNat 64 c) = state.memory (BitVec.ofNat 64 c)
    rw [hm_post]
    simp [Wave8Contracts.M26.updW, hne8, hne0]
  obtain ⟨hready_res, hwti_eq, hwo_eq, hne_eq⟩ :
      BmiReadyG resumed S0 Nd0 ∧
      worldTypedIvls resumed S0 Nd0 = worldTypedIvls state S0 Nd0 ∧
      worldOwned resumed S0 Nd0 = worldOwned state S0 Nd0 ∧
      nodeExtents resumed Nd0 = nodeExtents state Nd0 := by
    refine bmiReadyG_mpt_new q hreadyS0 hARs hARp hbe_mid hglob ?_ ?_ hq_hi hmono ?_
    · intro a hne
      change post.memory a ≠ state.memory a at hne
      rw [hm_post] at hne
      by_cases h8 : a = wm + 8#64
      · subst h8; right; rw [hp8_nat, hhp_st]
      · by_cases h0 : a = wm
        · subst h0; left; exact hhp_st
        · exfalso; apply hne; simp [Wave8Contracts.M26.updW, h8, h0]
    · exact ⟨by rw [hg_hp_r]; omega,
        le_of_eq (hg_ne_r "scratch_ptr" (bmi2_beq_ne_heap_names "scratch_ptr" (by decide)))⟩
    · intro nm hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
      rcases hnm with rfl | rfl | rfl
      · exact hlk_ne "slice_arr" (by decide)
      · exact hlk_ne "n" (by decide)
      · exact hlk_ne "out" (by decide)
  refine ⟨hARp, hmark_r, hm_r.trans hwm_mark, ⟨wm, by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩,
    ⟨ws, by rw [hlk_ne "slice_arr" (by decide)]; exact hws⟩,
    hn_r, hsa_r, hout_r, hle6, hle7,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hg_ne_r "keccak_pad" (bmi2_beq_ne_heap_names "keccak_pad" (by decide))]
  · rw [hg_ne_r "keccak_st" (bmi2_beq_ne_heap_names "keccak_st" (by decide))]
  · rw [hg_ne_r "frame_mem_ptr" (by decide)]
  · rw [hg_ne_r "mpt_hash_scratch" (bmi2_beq_ne_heap_names "mpt_hash_scratch" (by decide))]
  · rw [hg_ne_r "scratch_ptr" (bmi2_beq_ne_heap_names "scratch_ptr" (by decide))]
  ·
    have hdisj_m_s0 : ∀ iv ∈ worldOwned state S0 Nd0, Disj (locN state "mark", 16) iv := by
      intro iv hiv
      rcases bmi2_own_zero_or_inside state S0 Nd0 hreadyS0 iv hiv with rfl | hins | hins
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (by rw [← hmk]; exact hins.2)))
      · have hss : heapLimit ≤ scratchStart := by decide
        have hsp_lo : scratchStart ≤ globN state "scratch_ptr" := by
          have := hARs.2.2.2.1; have := hARs.2.2.2.2.1; omega
        have hmk_lim : locN state "mark" + 16 ≤ heapLimit := by
          rw [← hmk]; exact le_trans hmono hq_hi
        exact Or.inr (Or.inr (Or.inl (le_trans hmk_lim (le_trans hss (le_trans hsp_lo hins.1)))))
    refine ⟨S0, Nd0, [], hready_res.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Or.inl ⟨by rw [← hmk]; exact hR.1.1.2.1,
          by rw [← hmk, hg_hp_r]; exact hmono⟩
      · rw [← hwm_mark]
        exact P3MptSet.wordsOK_transfer hstep.1.1 hARp.1 hf.2.2
      · intro t ht i hi
        have hmem : i ∈ worldOwned resumed S0 Nd0 :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩))))
        rw [hwo_eq] at hmem
        exact hdisj_m_s0 i hmem
      · intro j hj
        have hmem : j ∈ worldOwned resumed S0 Nd0 :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
        rw [hwo_eq] at hmem
        exact hdisj_m_s0 j hmem
      · simp [NodeHeap]
      · have hroot_r : memW resumed (locN state "mark") = 0 := by
          rw [← hwm_mark]; exact hroot
        exact Or.inl hroot_r
      · simp [nodeExtents]
    · simp [NodeHeapValuePtrOK, NodeValuesSafe]
    · intro o ho j hj
      simp only [nodeExtents, List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at ho
      subst o
      have hmem : j ∈ worldOwned state S0 Nd0 := by
        rw [hne_eq] at hj
        exact List.mem_append.2 (Or.inr hj)
      exact hdisj_m_s0 j hmem
    · intro o ho j hj
      rcases List.mem_append.mp hj with hj | hj
      · rw [hwti_eq] at hj
        exact hdjRti o ho j hj
      · simp only [mptObjIvls, nodeExtents, List.flatMap_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hj
        subst j
        have hAs : ArenaOK state := hARs.2
        have hAp : ArenaOK resumed := hARp.2
        have hin16 : Inside (locN state "mark", 16) (globN state "heap_ptr") (globN resumed "heap_ptr") :=
          ⟨by rw [← hmk], by rw [← hmk, hg_hp_r]; exact hmono⟩
        exact Disj.flip (disj_fresh_heap_allocated hAs hAp hin16
          (bmi2_rti_zero_or_allocated state S0 Nd0 hreadyS0 o ho))
    · intro o ho j hj
      simp only [List.mem_singleton] at ho
      subst o
      rcases List.mem_append.mp hj with hj | hj
      · rw [hwo_eq] at hj
        exact hdjSlice _ (by simp) j hj
      · simp only [mptObjIvls, nodeExtents, List.flatMap_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hj
        subst j
        have h1 := hR.2.2.2.1.2
        rw [hmk] at h1
        exact Or.inr (Or.inr (Or.inl h1))
    · simp [nodeExtents]
    · intro o ho
      rw [hwo_eq] at ho
      exact Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
    · intro o ho
      rw [hwo_eq] at ho
      rcases bmi2_own_zero_or_inside state S0 Nd0 hreadyS0 o ho with h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h1.1, by rw [← hmk]; exact h1.2⟩)
      · exact Or.inr (Or.inr ⟨by rw [hg_ne_r "scratch_ptr"
          (bmi2_beq_ne_heap_names "scratch_ptr" (by decide))]; exact h2.1, h2.2⟩)
    · intro r hr hnz k hk hmiss
      simpa only [resumed, setVarHOLFinite, postCaller, memW] using
        hstep.2.2.2.1 r hr hnz k hk (fun i hi => by simp at hi)
    · intro i hi
      have hlt0 : locN state "slice_arr" + 16 * i < globN state "heap_ptr" := by
        have := hR.2.2.2.1.2; omega
      have hlt8 : locN state "slice_arr" + 16 * i + 8 < globN state "heap_ptr" := by
        have := hR.2.2.2.1.2; omega
      refine ⟨?_, ?_⟩
      · unfold memW; rw [hmem_lt_hp _ hlt0]
      · unfold memW; rw [hmem_lt_hp _ hlt8]
  · rw [← hmk]; exact hR.2.2.2.1.2
  · intro iv hiv
    exact bmi2_rti_zero_or_allocated state S0 Nd0 hreadyS0 iv hiv
  · rw [hg_ne_r "mpt_key_scratch" (bmi2_beq_ne_heap_names "mpt_key_scratch" (by decide))]
  · rw [hg_ne_r "mpt_key_scratch" (bmi2_beq_ne_heap_names "mpt_key_scratch" (by decide))]
    exact hkey
  · rw [hg_hp_r]
    exact ⟨hR.2.2.2.1.1, by have h2 := hR.2.2.2.1.2; have h3 := hmono; omega⟩
  · rw [← hsa_r, ← hn_r]
    exact hready_res.1.2.2.2.2.1
  · intro o ho j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact bmi2_slice_disj_rti state S0 Nd0 hreadyS0 o ho j hj
    · exact hdjSlice o ho j hj
  · intro i hi
    have h1 := hhp i hi
    rw [hmk] at h1
    exact h1
  · exact hkec
  · rw [hg_hp_r]
    have h1 := hmono
    have h2 := hmark_eq
    omega
end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

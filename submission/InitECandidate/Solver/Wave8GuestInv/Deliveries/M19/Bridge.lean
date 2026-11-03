import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.LightBatch
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.Reads

/-! Bridge between the light `Wave8M19` definitions and the split `Wave8GuestInv` rev9 modules. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.M19

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv

/-- Exact `FunSpec` and `OnReturn` from `Contracts.lean` (R10/R11). -/
def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

def HtabDelProgress : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F →
    Prop :=
  fun s post => hdr post (locN s "t") 3 + 1 = hdr s (locN s "t") 3 ∨
    post = { s with locals := post.locals, clock := post.clock }

def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ AllocatorGrows s post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    hdr post w.toNat 0 = locN s "key_len" ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

theorem freeChain_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) :
    ∀ head Fr, FreeChain s nodes head Fr ↔ Wave8M19.FreeChain s nodes head Fr
  | head, [] => Iff.rfl
  | head, f :: rest => by
    simp only [FreeChain, Wave8M19.FreeChain]
    exact and_congr Iff.rfl (freeChain_iff_light s nodes (nodeF s nodes f 0) rest)

theorem hdr_eq_light : @hdr = @Wave8M19.hdr := rfl
theorem nodeF_eq_light : @nodeF = @Wave8M19.nodeF := rfl
theorem memW_eq_light : @memW = @Wave8M19.memW := rfl
theorem htabFootprint_eq_light : @htabFootprint = @Wave8M19.htabFootprint := rfl
theorem Inside_eq_light : @Inside = @Wave8M19.Inside := rfl
theorem WordsOK_eq_light : @WordsOK = @Wave8M19.WordsOK := rfl
theorem maxKeyLen_eq_light : @maxKeyLen = @Wave8M19.maxKeyLen := rfl

theorem htab_pairwise_disj_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat)
    (h1 : 1 ≤ hdr s t 0) (hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8) :
    (htabFootprint s t).Pairwise Disj ↔ (Wave8M19.htabFootprint s t).Pairwise Wave8M19.Disj := by
  have hpos1 : 0 < (hdr s t 10 + 1) * hdr s t 1 := by
    have : 0 < hdr s t 1 := by omega
    exact Nat.mul_pos (Nat.succ_pos _) this
  have hpos2 : 0 < (hdr s t 10 + 1) * 32 := Nat.mul_pos (Nat.succ_pos _) (by decide)
  have hpos3 : 0 < (hdr s t 10 + 1) * 8 := Nat.mul_pos (Nat.succ_pos _) (by decide)
  have hnz : ∀ i ∈ htabFootprint s t, i.2 ≠ 0 := by
    simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl) <;> omega
  have hfp : Wave8M19.htabFootprint s t = htabFootprint s t := rfl
  rw [hfp]
  constructor
  · intro hp
    refine List.Pairwise.imp_of_mem ?_ hp
    intro a b ha hb hd
    rcases hd with h0 | h0 | h | h
    · exact absurd h0 (hnz a ha)
    · exact absurd h0 (hnz b hb)
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    refine List.Pairwise.imp_of_mem ?_ hp
    intro a b _ _ hd
    rcases hd with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem htabWF_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    HtabWF s t ↔ Wave8M19.HtabWF s t := by
  have hfree : FreeChain s = Wave8M19.FreeChain s := by
    funext nodes head Fr
    exact propext (freeChain_iff_light s nodes head Fr)
  unfold HtabWF Wave8M19.HtabWF
  simp only [hfree, hdr_eq_light, nodeF_eq_light, memW_eq_light, htabFootprint_eq_light,
    Inside_eq_light, WordsOK_eq_light, maxKeyLen_eq_light]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, rest⟩
    exact ⟨h1, (htab_pairwise_disj_iff s t h3 h5).mp h2, h3, h4, h5, rest⟩
  · rintro ⟨h1, h2, h3, h4, h5, rest⟩
    exact ⟨h1, (htab_pairwise_disj_iff s t h3 h5).mpr h2, h3, h4, h5, rest⟩

theorem arenaOK_to_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : ArenaOK s) : Wave8M19.ArenaOK s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

theorem arenaOK_from_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : Wave8M19.ArenaOK s) (hgw : GlobalsWord s) : ArenaOK s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, hgw⟩

theorem arg_to_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : HtabArgWF s) : Wave8M19.HtabArgWF s := by
  rcases h with ⟨⟨⟨c, m, sh, b⟩, ha⟩, hw, hal⟩
  exact ⟨⟨⟨c, m, sh, b⟩, arenaOK_to_light s ha⟩, (htabWF_iff_light s _).mp hw, hal⟩

theorem exit_from_light {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : Wave8M19.Htab.ExitR9 (Wave8M19.locN s "t") s post)
    (hgw : GlobalsWord s) : HtabExit s post := by
  rcases h with ⟨⟨⟨⟨c, m, sh, b⟩, ha⟩, hw, hh, hfp, hfr, _⟩, hk, hs, hg⟩
  exact ⟨⟨⟨c, m, sh, b⟩, arenaOK_from_light post ha (globalsWord_congr hg hgw)⟩,
    (htabWF_iff_light post _).mpr hw, hk, hs, hh, hfp, hfr,
    fun k _ => hg.symm ▸ rfl⟩

end InitECandidate.Solver.Wave8GuestInv.M19

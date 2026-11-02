import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.LightBatch
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.Reads

/-! Bridge between the light `Wave8M19` definitions and the R11 `Wave8GuestInv` definitions
(`MemoryViews.lean` + `ContractParts/C00.lean`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.HtabC00Ports

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv

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

theorem disj_iff_light_of_pos {i j : Ivl} (hi : 0 < i.2) (hj : 0 < j.2) :
    Disj i j ↔ Wave8M19.Disj i j := by
  simp only [Disj, Wave8M19.Disj]
  omega

theorem htabFootprint_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat)
    (hk1 : 1 ≤ hdr s t 0) (hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8) :
    ∀ i ∈ htabFootprint s t, 0 < i.2 := by
  have hstpos : 8 ≤ hdr s t 1 := by omega
  have h1 : 0 < (hdr s t 10 + 1) * hdr s t 1 := Nat.mul_pos (Nat.succ_pos _) (by omega)
  intro i hi
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · dsimp only; omega
  · exact h1
  · dsimp only; omega
  · dsimp only; omega

theorem pairwise_disj_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat)
    (hk1 : 1 ≤ hdr s t 0) (hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8) :
    (htabFootprint s t).Pairwise Disj ↔ (Wave8M19.htabFootprint s t).Pairwise Wave8M19.Disj := by
  have hpos := htabFootprint_pos s t hk1 hst
  rw [← htabFootprint_eq_light]
  constructor
  · intro hp
    exact List.Pairwise.imp_of_mem
      (fun {i j} hi hj h => (disj_iff_light_of_pos (hpos i hi) (hpos j hj)).mp h) hp
  · intro hp
    exact List.Pairwise.imp_of_mem
      (fun {i j} hi hj h => (disj_iff_light_of_pos (hpos i hi) (hpos j hj)).mpr h) hp

theorem htabWF_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    HtabWF s t ↔ Wave8M19.HtabWF s t := by
  have hfree : FreeChain s = Wave8M19.FreeChain s := by
    funext nodes head Fr
    exact propext (freeChain_iff_light s nodes head Fr)
  constructor
  · intro h
    obtain ⟨hfp, hdisj, hk1, hk60, hst, rest⟩ := h
    have hp := (pairwise_disj_iff_light s t hk1 hst).mp hdisj
    unfold Wave8M19.HtabWF
    simp only [← hfree, ← hdr_eq_light, ← nodeF_eq_light, ← memW_eq_light,
      ← htabFootprint_eq_light, ← Inside_eq_light, ← WordsOK_eq_light, ← maxKeyLen_eq_light]
    exact ⟨hfp, hp, hk1, hk60, hst, rest⟩
  · intro h
    obtain ⟨hfp, hdisj, hk1, hk60, hst, rest⟩ := h
    have hk1' : 1 ≤ hdr s t 0 := hk1
    have hst' : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hst
    have hp := (pairwise_disj_iff_light s t hk1' hst').mpr hdisj
    unfold HtabWF
    simp only [hfree, hdr_eq_light, nodeF_eq_light, memW_eq_light,
      htabFootprint_eq_light, Inside_eq_light, WordsOK_eq_light, maxKeyLen_eq_light]
    exact ⟨hfp, hp, hk1, hk60, hst, rest⟩

theorem globN_eq_light : @globN = @Wave8M19.globN := rfl
theorem locN_eq_light : @locN = @Wave8M19.locN := rfl
theorem Allocated_eq_light : @Allocated = @Wave8M19.Allocated := rfl
theorem FrameOutside_eq_light : @FrameOutside = @Wave8M19.FrameOutside := rfl

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
  rcases h with ⟨⟨⟨⟨c, m, sh, b⟩, ha⟩, hw, hh, hfp, hfo, hgl⟩, hk, hs⟩
  have hgw' : GlobalsWord post := by
    intro n hn
    by_cases hk : ofString n = ofString "heap_ptr"
    · have hgN : globN post n = globN post "heap_ptr" := by unfold globN; rw [hk]
      refine globalWord_of_globN_pos post n ?_
      rw [hgN]
      have : sourceBase ≤ globN post "heap_ptr" := ha.1
      have : sourceBase = 0xa1000000 := rfl
      omega
    · obtain ⟨w, hw⟩ := hgw n hn
      exact ⟨w, by
        unfold GlobalWord at hw ⊢
        have hne : ofString n ∉ (["heap_ptr"] : List String).map ofString := by simpa
        rw [← hgl _ hne]; exact hw⟩
  exact ⟨⟨⟨c, m, sh, b⟩, arenaOK_from_light post ha hgw'⟩,
    (htabWF_iff_light post _).mpr hw, hk, hs, hh, hfp, hfo, hgl⟩

end InitECandidate.Solver.Wave8GuestInv.HtabC00Ports

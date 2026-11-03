import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.SupportBase

set_option Elab.async false
namespace InitECandidate.Solver.Wave8GuestInv.HtabAstra
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- The copied recursive free-list predicates require an explicit transport. -/
theorem freeChain_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) :
    ∀ head Fr, FreeChain s nodes head Fr ↔ Wave8HtabAstra.FreeChain s nodes head Fr
  | head, [] => Iff.rfl
  | head, f :: rest => by
    simp only [FreeChain, Wave8HtabAstra.FreeChain]
    exact and_congr Iff.rfl (freeChain_iff_light s nodes (nodeF s nodes f 0) rest)

theorem hdr_eq_light : @hdr = @Wave8HtabAstra.hdr := rfl
theorem nodeF_eq_light : @nodeF = @Wave8HtabAstra.nodeF := rfl
theorem memW_eq_light : @memW = @Wave8HtabAstra.memW := rfl
theorem htabFootprint_eq_light : @htabFootprint = @Wave8HtabAstra.htabFootprint := rfl
theorem Inside_eq_light : @Inside = @Wave8HtabAstra.Inside := rfl
theorem WordsOK_eq_light : @WordsOK = @Wave8HtabAstra.WordsOK := rfl
theorem Disj_eq_light : @Disj = @Wave8HtabAstra.Disj := rfl
theorem maxKeyLen_eq_light : @maxKeyLen = @Wave8HtabAstra.maxKeyLen := rfl

theorem htabWF_iff_light {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    HtabWF s t ↔ Wave8HtabAstra.HtabWF s t := by
  have hfree : FreeChain s = Wave8HtabAstra.FreeChain s := by
    funext nodes head Fr
    exact propext (freeChain_iff_light s nodes head Fr)
  unfold HtabWF Wave8HtabAstra.HtabWF
  simp only [hfree, hdr_eq_light, nodeF_eq_light, memW_eq_light, htabFootprint_eq_light,
    Inside_eq_light, WordsOK_eq_light, Disj_eq_light, maxKeyLen_eq_light]

theorem globN_eq_light : @globN = @Wave8HtabAstra.globN := rfl
theorem locN_eq_light : @locN = @Wave8HtabAstra.locN := rfl
theorem Allocated_eq_light : @Allocated = @Wave8HtabAstra.Allocated := rfl
theorem FrameOutside_eq_light : @FrameOutside = @Wave8HtabAstra.FrameOutside := rfl

theorem arenaOK_to_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : ArenaOK s) : Wave8HtabAstra.ArenaOK s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

theorem arenaOK_from_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : Wave8HtabAstra.ArenaOK s) (hgw : GlobalsWord s) : ArenaOK s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, hgw⟩

theorem arg_to_light {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : HtabArgWF s) : Wave8HtabAstra.HtabArgWF s := by
  rcases h with ⟨⟨⟨c, m, sh, b⟩, ha⟩, hw, hal⟩
  exact ⟨⟨⟨c, m, sh, b⟩, arenaOK_to_light s ha⟩, (htabWF_iff_light s _).mp hw, hal⟩

end InitECandidate.Solver.Wave8GuestInv.HtabAstra

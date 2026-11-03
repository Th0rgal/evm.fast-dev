import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.FullBridge
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.DelFinal

/-! Exact revision-9 audit. audit.py pins the source and selects its dedicated artifact.
This batch checks both exact target contract types and their trusted-axiom closure. -/
set_option Elab.async false
open Flapjack Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.Wave8GuestInv
example {F : Type} (s post : PanSemStateFiniteExact 64 F) (h : HtabExit s post) :
    hdr post (locN s "t") 0 = hdr s (locN s "t") 0 := h.2.2.1
example {F : Type} (s post : PanSemStateFiniteExact 64 F) (h : HtabExit s post) :
    hdr post (locN s "t") 1 = hdr s (locN s "t") 1 := h.2.2.2.1





/-! Transport the light-cone progress proof to the exact fixed-spec predicates. -/
namespace InitECandidate.Solver.Wave8GuestInv.HtabAstra
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem htab_del_progress_spec_proof :
    FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del") := by
  rcases Wave8HtabAstra.Htab.htab_del_progress_spec_proof with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hpre _ hnt v hv
  exact hrun s hc (arg_to_light s hpre) hnt v hv

example : type_of% htab_del_progress_spec := htab_del_progress_spec_proof
end InitECandidate.Solver.Wave8GuestInv.HtabAstra


/-! Transport the deletion invariant proof to the frozen revision-9 contract.
The named predicates are checked against the canonical full-spec import in Progress. -/
namespace InitECandidate.Solver.Wave8GuestInv.HtabAstra
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem exit_from_light {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : Wave8HtabAstra.Htab.ExitR9 (Wave8HtabAstra.locN s "t") s post)
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

theorem htab_del_spec_proof :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del") := by
  rcases Wave8HtabAstra.Htab.htab_del_spec_proof with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hpre _ hnt v hv
  exact exit_from_light s _ (hrun s hc (arg_to_light s hpre) hnt v hv) hpre.1.2.2.2.2.2.2.2.2.2

example : type_of% htab_del_spec := htab_del_spec_proof
end InitECandidate.Solver.Wave8GuestInv.HtabAstra

import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs

/-! # Wave 8 R31 S1: Chain-WF handler specs for the remaining opcodes (part A)

`OpHandlerChainSpec` leaves, proof-complete, for the Group 01-03 opcodes, proved with the
`Group09ChainWF.HandlerRunA` combinator framework and read-only `epsA_of_readOnly`
callee leaves.  Companion to `StrongBridgesR29.RemainingChainHandlersR29`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09ChainWF

/-! ## 1. `epsA` leaves for read-only arithmetic callees -/

theorem epsA_u256_is_zero :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_is_zero") :=
  epsA_of_readOnly 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_eq :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_eq") :=
  epsA_of_readOnly 45 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_eq rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_lt :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_lt") :=
  epsA_of_readOnly 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_gt :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_gt") :=
  epsA_of_readOnly 47 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_gt rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_slt :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_slt") :=
  epsA_of_readOnly 48 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_slt rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_sgt :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_sgt") :=
  epsA_of_readOnly 49 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sgt rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_add :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_add") :=
  epsA_of_readOnly 56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_sub :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_sub") :=
  epsA_of_readOnly 57 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sub rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_mul :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_mul") :=
  epsA_of_readOnly 60 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_exp :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_exp") :=
  epsA_of_readOnly 80 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_exp rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_shl :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_shl") :=
  epsA_of_readOnly 81 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_shl rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_shr :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_shr") :=
  epsA_of_readOnly 82 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_shr rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_sar :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_sar") :=
  epsA_of_readOnly 83 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sar rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_signextend :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_signextend") :=
  epsA_of_readOnly 84 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_signextend rfl opRoCallees opRoCallees_good rfl

theorem epsA_u256_byte :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_byte") :=
  epsA_of_readOnly 85 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte rfl opRoCallees opRoCallees_good rfl

/-! ## 2. `stack_push` leaf transported from the `Group10` framework -/

theorem hmw_g10_to_g09 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : R16Shards.OpHandlersB.Group10.HeadMemChainWF s) :
    R16Shards.OpHandlersB.Group09ChainWF.HeadMemChainWF s :=
  (headMemChainWF_g09_iff_bridge s).mpr ((headMemChainWF_g10_iff_bridge s).mp h)

theorem epsA_stack_push_g09 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push") := by
  obtain ⟨params, body, retShape, hlk, hsp⟩ := epsA_stack_push
  refine ⟨params, body, retShape, hlk, ?_⟩
  intro F s hc hInv hWF hP hlkv hnt
  have hsp' := hsp s hc hInv
    ((headMemChainWF_g10_iff_bridge s).mpr ((headMemChainWF_g09_iff_bridge s).mp hWF)) hP hlkv hnt
  dsimp only at hsp' ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · exact And.imp (fun h1 => ⟨h1.1, hmw_g10_to_g09 h1.2⟩) (fun h2 => h2) (hsp'.1 v hv)
  · exact And.imp (fun h1 => ⟨h1.1, hmw_g10_to_g09 h1.2⟩) (fun h2 => h2) (hsp'.2 herr)

/-! ## 2.5 `epsA` lift of the workspace (`u256_ws`) callee judgment -/

theorem lookup_two_comb4_locals_g31 {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ a0 a1 a2 a3, callee.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) ∧
    (∃ b0 b1 b2 b3, callee.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.1)
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2)
      refine ⟨hb, ⟨a0, a1, a2, a3, ?_⟩, ⟨b0, b1, b2, b3, ?_⟩⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "a" ≠ ofString "b" by decide] using congrFun hfn (ofString "a")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "b")
    · simp at hraw
  · simp [List.length] at hraw

theorem call_u256_divmod_wsSafe_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_divmod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, ⟨b0, b1, b2, b3, hb_c⟩⟩ := lookup_two_comb4_locals_g31 lookup_u256_divmod hl
  exact u256_divmod_wsSafe (he.with_locals_clock callee _) hb_c

private theorem lookup_u256_div_g31 :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_div).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_u256_mod_g31 :
    originalRuntimeCode.lookup (ofString "u256_mod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 71 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mod) rfl

private theorem call_u256_div_wsSafe_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_div") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, _⟩ := lookup_two_comb4_locals_g31 lookup_u256_div_g31 hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe_g31 (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

theorem call_u256_mod_wsSafe_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_mod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, _⟩ := lookup_two_comb4_locals_g31 lookup_u256_mod_g31 hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe_g31 (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

theorem epsA_of_wsSafe_g31 (idx : Nat) (hidx : idx < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WsEnv s s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString (extractFn d).name) values =
          some (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
                s.locals,
                InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape)) →
      WsSafe s (untypedGlobalBufIvls s)
        (evaluateHOLFiniteState s
          (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body))) :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True)
      (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s hcode hInv hWF _ hlkv _
  have hsafe := hbody s (WsEnv.of_evmInv hcode hInv) hlkv
  have hres (hr : Resumes (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).1) :
      let post := (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
      (EvmInv post ∧ HeadMemChainWF post) ∧
        evmChain post = evmChain s ∧ evmR post ≤ evmR s := by
    dsimp only
    have heff := hsafe.2 hr
    obtain ⟨hInv_p, hg, hch, hR⟩ := evmStepR_of_untypedGlobalBufs hInv heff
    have hInvC := hInv
    obtain ⟨hAs, S, hW, hrest⟩ := hInvC
    have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
    have hF := hW.2.2.1
    have hub_map : ∀ x ∈ untypedGlobalBufIvls s,
        x ∈ globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
      intro x hx
      unfold untypedGlobalBufIvls at hx
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩
      · exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
      · exact List.mem_map.2 ⟨("keccak_pad", 136), by decide, rfl⟩
      · exact List.mem_map.2 ⟨("keccak_st", 200), by decide, rfl⟩
      · exact List.mem_map.2 ⟨("mpt_nib_scratch", 64), by decide, rfl⟩
    have hfix : ∀ x ∈ untypedGlobalBufIvls s, x ∈ fixedObjects s := fun x hx => by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (hub_map x hx)))
    have hRl8 : ∀ i ∈ untypedGlobalBufIvls s, i.1 % 8 = 0 := by
      intro i hi
      rcases hF.1 i (hfix i hi) with h0 | ⟨_, hw⟩
      · obtain ⟨gn, hgn_m, rfl⟩ := List.mem_map.1 (hub_map i hi)
        have hpos : 0 < gn.2 := by clear * - hgn_m; revert gn hgn_m; decide
        dsimp only at h0 ⊢
        by_cases hz : globN s gn.1 = 0
        · simp [hz]
        · simp [hz] at h0; omega
      · exact hw.1
    have hdj_all : IvlsDisj (untypedGlobalBufIvls s)
        (((evmChain s).map (frameObjects s)).flatten) := by
      intro x hx j hj
      have hx_fix := hfix x hx
      obtain ⟨fo, hfo_map, hj_fo⟩ := List.mem_flatten.1 hj
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
      exact R11Shards.Disj.symm ((hInvAt.2.2.2.2.2.2.2.2.1 ec hec j hj_fo).2 x hx_fix)
    have hdj : ∀ ec ∈ evmChain s, ∀ i ∈ untypedGlobalBufIvls s,
        (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i) := by
      intro ec hec i hi
      have hm280 : (ec.1, 280) ∈ frameObjects s ec := by simp [frameObjects]
      have hm104 : (ec.2, 104) ∈ frameObjects s ec := by simp [frameObjects]
      exact ⟨Or.inr (R11Shards.Disj.symm (hdj_all i hi _ (List.mem_flatten.2 ⟨frameObjects s ec,
        List.mem_map.2 ⟨ec, hec, rfl⟩, hm280⟩))),
        Or.inr (R11Shards.Disj.symm (hdj_all i hi _ (List.mem_flatten.2 ⟨frameObjects s ec,
        List.mem_map.2 ⟨ec, hec, rfl⟩, hm104⟩)))⟩
    have hWF_p := headMemChainWF_of_disj_bre hInv hWF hch
        (congrFun (globN_congr hg) "ev") (congrFun (globN_congr hg) "frame_mem_ptr")
        hRl8 heff.cell_frame hdj
    exact ⟨⟨hInv_p, hWF_p⟩, hch, le_of_eq hR⟩
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hres (Or.inl ⟨v, hv⟩)
    exact ⟨h1, h2, h3, trivial⟩
  · obtain ⟨v, hv⟩ := herr
    exact hres (Or.inr ⟨_, v, hv, by decide⟩)

theorem epsA_u256_div :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True) (ofString "u256_div") :=
  epsA_of_wsSafe_g31 70 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_div rfl
    (fun {F} s he _ => by
      dsimp only [extractFn, Guest.Software.guestFn_u256_div,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
        Option.map, List.map]
      refine WsSafe.decCall ?_ ?_
      · intro vals body callee rs _ hl _
        exact call_u256_divmod_wsSafe_g31 he hl
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _
        exact WsSafe.return_exp _ _ _)

theorem epsA_u256_mod :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True) (ofString "u256_mod") :=
  epsA_of_wsSafe_g31 71 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mod rfl
    (fun {F} s he _ => by
      dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
        Option.map, List.map]
      refine WsSafe.decCall ?_ ?_
      · intro vals body callee rs _ hl _
        exact call_u256_divmod_wsSafe_g31 he hl
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _
        exact WsSafe.return_exp _ _ _)

theorem epsA_u256_sdiv :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True) (ofString "u256_sdiv") :=
  epsA_of_wsSafe_g31 73 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sdiv rfl
    (fun {F} s he _ => by
      dsimp only [extractFn, Guest.Software.guestFn_u256_sdiv,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
        Option.map, List.map]
      refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
      intro _ heff0
      have he1 := he.step heff0
      refine WsSafe.decCall_ro he1 (by decide) fun _ _ he2 _ _ => ?_
      refine WsSafe.decCall_ro he2 (by decide) fun _ _ he3 _ _ => ?_
      refine WsSafe.decCall ?_ ?_
      · intro vals body callee rs _ hl _
        exact call_u256_div_wsSafe_g31 he3 hl
      · intro _ _ _ _ vq cpost _ _ _ _ heff_q _ _
        exact WsSafe.of_readOnly (he3.step heff_q).code (by decide))

theorem epsA_u256_smod :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True) (ofString "u256_smod") :=
  epsA_of_wsSafe_g31 74 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_smod rfl
    (fun {F} s he _ => by
      dsimp only [extractFn, Guest.Software.guestFn_u256_smod,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
        Option.map, List.map]
      refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
      intro _ heff0
      have he1 := he.step heff0
      refine WsSafe.decCall_ro he1 (by decide) fun _ _ he2 _ _ => ?_
      refine WsSafe.decCall_ro he2 (by decide) fun _ _ he3 _ _ => ?_
      refine WsSafe.decCall ?_ ?_
      · intro vals body callee rs _ hl _
        exact call_u256_mod_wsSafe_g31 he3 hl
      · intro _ _ _ _ vr cpost _ _ _ _ heff_r _ _
        exact WsSafe.of_readOnly (he3.step heff_r).code (by decide))

/-! ## 3. Pilot handler: `op_add` -/

theorem op_add_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_add") := by
  refine opHandlerSpecA_of_run 475 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_add rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_add, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · refine HandlerRunA.decCall_simple epsA_u256_add ?_
    refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
    exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

/-! ## 4. End-to-end bridge check -/

theorem op_add_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_add") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_add_specA)

/-! ## 3. Generalized Group10 → Group09ChainWF transport + remaining shared leaves -/

theorem epsA_g10_to_g09 {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS}
    (h : R16Shards.OpHandlersB.EvmPreservingSpecA P Qret fname) :
    Group09ChainWF.EvmPreservingSpecA P Qret fname := by
  obtain ⟨params, body, retShape, hlk, hsp⟩ := h
  refine ⟨params, body, retShape, hlk, ?_⟩
  intro F s hc hInv hWF hP hlkv hnt
  have hsp' := hsp s hc hInv
    ((headMemChainWF_g10_iff_bridge s).mpr ((headMemChainWF_g09_iff_bridge s).mp hWF)) hP hlkv hnt
  dsimp only at hsp' ⊢
  exact ⟨fun v hv => And.imp (fun h1 => ⟨h1.1, hmw_g10_to_g09 h1.2⟩) (fun h2 => h2) (hsp'.1 v hv),
    fun herr => And.imp (fun h1 => ⟨h1.1, hmw_g10_to_g09 h1.2⟩) (fun h2 => h2) (hsp'.2 herr)⟩

theorem epsA_sat_word_g09 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "sat_word") := epsA_g10_to_g09 epsA_sat_word

theorem epsA_stack_push_word_g09 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_word") := epsA_g10_to_g09 epsA_stack_push_word

theorem epsA_stack_push_bool_g09 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_bool") := epsA_g10_to_g09 epsA_stack_push_bool

theorem epsA_u256_bit_length :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_bit_length") :=
  epsA_of_readOnly 78 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit_length rfl
    opRoCallees opRoCallees_good rfl

theorem op_mul_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_mul") := by
  refine opHandlerSpecA_of_run 476 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mul rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_mul, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_mul ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_mul_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mul") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_mul_specA)

theorem op_sub_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_sub") := by
  refine opHandlerSpecA_of_run 477 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sub rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_sub, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_sub ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_sub_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sub") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_sub_specA)

theorem op_div_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_div") := by
  refine opHandlerSpecA_of_run 478 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_div rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_div, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_div ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_div_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_div") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_div_specA)

theorem op_sdiv_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_sdiv") := by
  refine opHandlerSpecA_of_run 479 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sdiv rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_sdiv, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_sdiv ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_sdiv_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sdiv") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_sdiv_specA)

theorem op_mod_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_mod") := by
  refine opHandlerSpecA_of_run 480 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mod rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_mod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_mod ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_mod_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mod") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_mod_specA)

theorem op_smod_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_smod") := by
  refine opHandlerSpecA_of_run 481 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_smod rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_smod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_smod ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_smod_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_smod") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_smod_specA)

theorem op_signextend_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_signextend") := by
  refine opHandlerSpecA_of_run 485 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_signextend rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_signextend, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_sat_word_g09 ?_
  refine HandlerRunA.decCall_simple epsA_u256_signextend ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_signextend_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_signextend") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_signextend_specA)

theorem op_lt_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_lt") := by
  refine opHandlerSpecA_of_run 486 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_lt rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_lt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_lt ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_lt_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_lt") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_lt_specA)

theorem op_gt_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_gt") := by
  refine opHandlerSpecA_of_run 487 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gt rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_gt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_gt ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_gt_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gt") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_gt_specA)

theorem op_slt_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_slt") := by
  refine opHandlerSpecA_of_run 488 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_slt rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_slt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_slt ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_slt_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slt") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_slt_specA)

theorem op_sgt_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_sgt") := by
  refine opHandlerSpecA_of_run 489 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sgt rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_sgt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_sgt ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_sgt_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sgt") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_sgt_specA)

theorem op_eq_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_eq") := by
  refine opHandlerSpecA_of_run 490 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_eq rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_eq, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_eq ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_eq_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_eq") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_eq_specA)

theorem op_iszero_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_iszero") := by
  refine opHandlerSpecA_of_run 491 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_iszero rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_iszero, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_is_zero ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_bool_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_iszero_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_iszero") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_iszero_specA)

theorem op_and_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_and") := by
  refine opHandlerSpecA_of_run 492 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_and rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_and, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_and_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_and") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_and_specA)

theorem op_or_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_or") := by
  refine opHandlerSpecA_of_run 493 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_or rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_or, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_or_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_or") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_or_specA)

theorem op_xor_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_xor") := by
  refine opHandlerSpecA_of_run 494 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_xor rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_xor, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_xor_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_xor") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_xor_specA)

theorem op_not_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_not") := by
  refine opHandlerSpecA_of_run 495 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_not rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_not, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_not_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_not") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_not_specA)

theorem op_byte_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_byte") := by
  refine opHandlerSpecA_of_run 496 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_byte rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_byte, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_sat_word_g09 ?_
  refine HandlerRunA.decCall_simple epsA_u256_byte ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_word_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_byte_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_byte") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_byte_specA)

theorem op_shl_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_shl") := by
  refine opHandlerSpecA_of_run 497 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_shl rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_shl, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_sat_word_g09 ?_
  refine HandlerRunA.decCall_simple epsA_u256_shl ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_shl_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shl") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_shl_specA)

theorem op_shr_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_shr") := by
  refine opHandlerSpecA_of_run 498 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_shr rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_shr, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_sat_word_g09 ?_
  refine HandlerRunA.decCall_simple epsA_u256_shr ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_shr_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shr") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_shr_specA)

theorem op_sar_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_sar") := by
  refine opHandlerSpecA_of_run 499 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sar rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_sar, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_sat_word_g09 ?_
  refine HandlerRunA.decCall_simple epsA_u256_sar ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_sar_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sar") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_sar_specA)

theorem op_clz_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_clz") := by
  refine opHandlerSpecA_of_run 500 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_clz rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_clz, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  refine HandlerRunA.decCall_simple epsA_u256_bit_length ?_
  refine HandlerRunA.seq_call_simple epsA_stack_push_word_g09 ?_
  exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_clz_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_clz") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_clz_specA)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A

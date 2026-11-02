import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas
import Guest.SoftwareAst

/-! `ek_charge_gas`: `charge_gas` (AST index 448, line 14949) satisfies
`EvmKeeps EvmInv [] (ofString "charge_gas")` on spec R11. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.M21

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M23

private theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem scratchEnd_val : scratchEnd = 2965299200 := rfl

private theorem evmStep_of_lc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (heq : post = { s with locals := post.locals, clock := post.clock }) :
    EvmStep [] s post := by
  have hGp : GuestInv post := by
    rw [heq]; exact guestInv_with_locals_clock s post.locals post.clock hE.1.1
  apply evmStep_of_head_16_64_184 hE hGp (by rw [heq]) (by rw [heq])
  · intro x _ _ _; rw [heq]
  · unfold memW; rw [heq]
  · unfold memW; rw [heq]

theorem lookup_charge_gas :
    originalRuntimeCode.lookup (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFnBody Guest.Software.guestFn_charge_gas, .one) :=
  lookup_of_guestAst_getElem 448 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_charge_gas) rfl

/-- `charge_gas` (AST index 448, line 14949): EVM step keeping `EvmInv`, globals, and `evmChain`. -/
theorem «ek_charge_gas» :
    EvmKeeps EvmInv [] (ofString "charge_gas") := by
  refine ⟨_, _, _, lookup_charge_gas, ?_⟩
  intro F s hcode hE _hlookup _ hres
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_gas,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i glv hgl
    have hgl_info : ∃ (evw glw : BitVec 64),
        s.globals.lookup (ofString "ev") = some (.val (.word evw)) ∧
        glv = .val (.word glw) ∧
        evw + BitVec.ofNat 64 64 = BitVec.ofNat 64 (globN s "ev" + 64) ∧
        glw.toNat = memW s (globN s "ev" + 64) := by
      simp [evalHOLExact, evalListHOLExact] at hgl
      rcases hev : s.globals.lookup (ofString "ev") with _ | ev_val
      · simp [hev] at hgl
      · rcases ev_val with ⟨⟨evw⟩⟩ | _ | _
        · simp [hev, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hgl
          rcases hm : s.memory (evw + BitVec.ofNat 64 64) with ⟨glw⟩
          rw [hm] at hgl
          have hadd : BitVec.ofNat 64 (evw.toNat + 64) = evw + BitVec.ofNat 64 64 := by
            rw [BitVec.add_def]; simp
          exact ⟨evw, glw, rfl, hgl.2.symm, by simp [globN, hev, hadd], by simp [globN, memW, hev, hadd, hm]⟩
        · simp [hev, valueIsWord] at hgl
        · simp [hev, valueIsWord] at hgl
    obtain ⟨evw, glw, hevw, rfl, hev64, hglw_eq⟩ := hgl_info
    split
    · set s1 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s with hs1
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      split
      · rename_i cw hcond
        split
        · rename_i hcw0
          subst hcw0
          have hamt_info : ∃ amtw : BitVec 64,
              s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) ∧
              amtw.toNat ≤ glw.toNat := by
            have hgl1 : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
              simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            simp only [evalHOLExact, hgl1] at hcond
            rcases hamt : s1.locals.lookup (ofString "amount") with _ | av
            · simp [hamt] at hcond
            · rcases av with ⟨⟨amtw⟩⟩ | _ | _
              · simp only [hamt, Compiler.Encoders.Asm.wordCmpHOL] at hcond
                refine ⟨amtw, rfl, ?_⟩
                by_cases hlt : glw < amtw
                · simp [hlt] at hcond
                · rw [BitVec.lt_def] at hlt; omega
              · simp [hamt] at hcond
              · simp [hamt] at hcond
          obtain ⟨amtw, hamt1, hamt_le⟩ := hamt_info
          rw [evaluateHOLFiniteState_skip]
          dsimp only
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
          split
          · rename_i addr1 haddr1
            have haddr1_eq : addr1 = evw + BitVec.ofNat 64 64 := by
              simp [hs1, setVarHOLFinite, evalHOLExact, evalListHOLExact, hevw,
                valueIsWord, valueWord, wordOpHOL, wordOp] at haddr1
              exact haddr1.symm
            subst haddr1_eq
            split
            · rename_i val1 hval1
              have hgl1 : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
                simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hval1_eq : val1 = .val (.word (glw - amtw)) := by
                simp [evalHOLExact, evalListHOLExact, hgl1, hamt1, valueIsWord, valueWord,
                  wordOpHOL, wordOp] at hval1
                exact hval1.symm
              subst hval1_eq
              split
              · rename_i mem1 hmem1
                dsimp only
                have hmem1_spec : mem1 (evw + BitVec.ofNat 64 64) = .word (glw - amtw) ∧
                    ∀ x, x ≠ evw + BitVec.ofNat 64 64 → mem1 x = s.memory x := by
                  simp only [hs1, setVarHOLFinite, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem1
                  split at hmem1
                  · rename_i upd1 hupd1
                    injection hmem1 with hmem1
                    subst hmem1
                    split at hupd1
                    · injection hupd1 with hupd1
                      rw [← hupd1]
                      exact ⟨if_pos rfl, fun x hx => if_neg hx⟩
                    · simp at hupd1
                  · simp at hmem1
                set s2 : PanSemStateFiniteExact 64 F := { s1 with memory := mem1 }
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
                split
                · rename_i addr2 haddr2
                  have haddr2_eq : addr2 = evw + BitVec.ofNat 64 184 := by
                    simp [s2, hs1, setVarHOLFinite, evalHOLExact, evalListHOLExact, hevw,
                      valueIsWord, valueWord, wordOpHOL, wordOp] at haddr2
                    exact haddr2.symm
                  subst haddr2_eq
                  split
                  · rename_i val2 hval2
                    have hval2_word : ∃ w2 : BitVec 64, val2 = .val (.word w2) := by
                      simp only [evalHOLExact, evalListHOLExact] at hval2
                      rcases hl184 : @evalHOLExact 64 F _ s2.toExact
                          (fun a => Classical.propDecidable (s2.memaddrs a))
                          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])) with _ | v184
                      · simp only [evalHOLExact, evalListHOLExact] at hl184
                        rw [hl184] at hval2; simp at hval2
                      · simp only [evalHOLExact, evalListHOLExact] at hl184
                        rw [hl184, hamt1] at hval2
                        rcases v184 with ⟨⟨w0⟩⟩ | _ | _
                        · simp [valueIsWord, valueWord, wordOpHOL, wordOp] at hval2
                          exact ⟨_, hval2.symm⟩
                        · simp [List.all, valueIsWord] at hval2
                        · simp [List.all, valueIsWord] at hval2
                    obtain ⟨w2, rfl⟩ := hval2_word
                    split
                    · rename_i mem2 hmem2
                      dsimp only
                      have hmem2_spec : ∀ x, x ≠ evw + BitVec.ofNat 64 184 → mem2 x = mem1 x := by
                        simp only [s2, hs1, setVarHOLFinite, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem2
                        split at hmem2
                        · rename_i upd2 hupd2
                          injection hmem2 with hmem2
                          subst hmem2
                          split at hupd2
                          · injection hupd2 with hupd2
                            rw [← hupd2]
                            exact fun x hx => if_neg hx
                          · simp at hupd2
                        · simp at hmem2
                      set s3 : PanSemStateFiniteExact 64 F := { s2 with memory := mem2 }
                      rw [evaluateHOLFiniteState_return]
                      split
                      · intro h; exact absurd h not_resumes_error
                      · split
                        · intro _
                          set post := { (emptyLocalsHOLFinite s3) with
                              locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s3).locals
                                (ofString "gl", s.locals.lookup (ofString "gl")) }
                          have hev184 : evw + BitVec.ofNat 64 184 = BitVec.ofNat 64 (globN s "ev" + 184) := by
                            have hadd : BitVec.ofNat 64 (evw.toNat + 184) = evw + BitVec.ofNat 64 184 := by
                              rw [BitVec.add_def]; simp
                            simp [globN, hevw, hadd]
                          have he_lt : globN s "ev" + 280 < 2 ^ 64 := by
                            obtain ⟨_, _, _, _, _, _, hFWF, _⟩ := hE
                            have he_in := (hFWF (globN s "ev", globN s "cur_cont")
                              (by simp [evmChain, evmChainFrom])).1 (globN s "ev", 280) (by simp) |>.1
                            have := he_in.2; rw [scratchEnd_val] at this; omega
                          have hne_64_184 : BitVec.ofNat 64 (globN s "ev" + 64) ≠
                              BitVec.ofNat 64 (globN s "ev" + 184) := by
                            intro heq
                            have := congrArg BitVec.toNat heq
                            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
                            omega
                          have hne_16_64 : BitVec.ofNat 64 (globN s "ev" + 16) ≠
                              BitVec.ofNat 64 (globN s "ev" + 64) := by
                            intro heq
                            have := congrArg BitVec.toNat heq
                            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
                            omega
                          have hne_16_184 : BitVec.ofNat 64 (globN s "ev" + 16) ≠
                              BitVec.ofNat 64 (globN s "ev" + 184) := by
                            intro heq
                            have := congrArg BitVec.toNat heq
                            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
                            omega
                          have hGp : GuestInv post :=
                            guestInv_congr (s := s) rfl rfl rfl rfl hE.1.1
                          have hmem_out : ∀ x : BitVec 64,
                              x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
                              x ≠ BitVec.ofNat 64 (globN s "ev" + 64) →
                              x ≠ BitVec.ofNat 64 (globN s "ev" + 184) →
                              post.memory x = s.memory x := by
                            intro x _ hx1 hx2
                            change mem2 x = s.memory x
                            rw [hmem2_spec x (hev184 ▸ hx2), hmem1_spec.2 x (hev64 ▸ hx1)]
                          have hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16) := by
                            unfold memW
                            have hm16 : post.memory (BitVec.ofNat 64 (globN s "ev" + 16)) =
                                s.memory (BitVec.ofNat 64 (globN s "ev" + 16)) := by
                              change mem2 _ = s.memory _
                              rw [hmem2_spec _ (hev184 ▸ hne_16_184), hmem1_spec.2 _ (hev64 ▸ hne_16_64)]
                            rw [hm16]
                          have hgas_le : memW post (globN s "ev" + 64) ≤ memW s (globN s "ev" + 64) := by
                            have hm64 : post.memory (BitVec.ofNat 64 (globN s "ev" + 64)) = .word (glw - amtw) := by
                              change mem2 (BitVec.ofNat 64 (globN s "ev" + 64)) = _
                              rw [hmem2_spec _ (hev184 ▸ hne_64_184), ← hev64, hmem1_spec.1]
                            have hpost64 : memW post (globN s "ev" + 64) = (glw - amtw).toNat := by
                              unfold memW; rw [hm64]
                            rw [hpost64, ← hglw_eq, BitVec.toNat_sub_of_le (BitVec.le_def.mpr hamt_le)]
                            omega
                          exact evmStep_of_head_16_64_184 hE hGp rfl rfl hmem_out hsp_le hgas_le
                        · intro h; exact absurd h not_resumes_error
                    · intro h; exact absurd h not_resumes_error
                  · intro h; exact absurd h not_resumes_error
                · intro h; exact absurd h not_resumes_error
              · intro h; exact absurd h not_resumes_error
            · intro h; exact absurd h not_resumes_error
          · intro h; exact absurd h not_resumes_error
        · rcases hraise : evaluateHOLFiniteState s1
              (.raise (ofString "EvmErr") (.const (BitVec.ofNat 64 4))) with ⟨rr, sr⟩
          have hr_spec : (∃ v, rr = some (.exception (ofString "EvmErr") v) ∧ sr = emptyLocalsHOLFinite s1) ∨
              rr = some .error := by
            rw [evaluateHOLFiniteState_raise] at hraise
            split at hraise
            · dsimp only at hraise
              split at hraise
              · injection hraise with h1 h2; exact Or.inl ⟨_, h1.symm, h2.symm⟩
              · injection hraise with h1 _; exact Or.inr h1.symm
            · injection hraise with h1 _; exact Or.inr h1.symm
          rcases hr_spec with ⟨v, rfl, rfl⟩ | rfl
          · dsimp only
            intro _
            exact evmStep_of_lc hE rfl
          · dsimp only
            intro h; exact absurd h not_resumes_error
      · intro h; exact absurd h not_resumes_error
    · intro h; exact absurd h not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.M21

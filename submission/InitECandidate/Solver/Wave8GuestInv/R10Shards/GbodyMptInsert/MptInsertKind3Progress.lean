import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Branch

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestGlobalKeep

theorem mpt_branch_finish_none {F : Type} (s u v t : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (n : BitVec 64)
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hm : n.toNat ∈ Nd)
    (hk : memW s n.toNat = 3)
    (hnode : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (hle : locN s "level" ≤ locN s "klen")
    (hkey : KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hslot : MptSlotOK s Nd) (hvlen : locN s "vlen" < 2 ^ 40)
    (hklen : locN s "klen" ≤ 64) (hgo : locN s "go" = 0)
    (hb : evaluateHOLFiniteState s mptInsertBranch = (none, u))
    (hvS : v = {u with locals := v.locals})
    (hvLoc : ∀ name ∈ ["go", "node", "slot", "level", "r", "next_node", "next_slot", "next_level", "key", "klen", "vlen"],
      v.locals.lookup (ofString name) = u.locals.lookup (ofString name))
    (hf : evaluateHOLFiniteState v mptInsertFinish = (none, t)) :
    MptInsertHead t ∧ (locN t "go" = 0 ∨ locN s "level" < locN t "level") := by
  obtain ⟨w, hw, hcase⟩ := mpt_ite_none_inv hb
  obtain ⟨l, kl, hl, hkl, hc⟩ := evalAt_cmp s .equal _ _ w hw
  have hlN := evalAt_local s "level" l hl
  have hklN := evalAt_local s "klen" kl hkl
  change s.locals.lookup (ofString "level") = some (.val (.word l)) at hl
  change s.locals.lookup (ofString "klen") = some (.val (.word kl)) at hkl
  have hc' : w = if l = kl then 1 else 0 := by
    simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hc
  rw [hc'] at hcase
  by_cases heq : l = kl
  · simp only [heq, ↓reduceIte] at hcase
    change evaluateHOLFiniteState s mptInsertPayload = (none, u) at hcase
    have haU := mpt_arena_local_program s mptInsertPayload ha (fun _ => by rfl)
    rw [hcase] at haU
    have haV : ArenaReady v := by
      rw [hvS]; exact (arenaReady_with_locals u v.locals u.clock).2 haU
    have hgoU := mpt_avoids_none s u mptInsertPayload (ofString "go") (by decide) hcase
    have hgoV : locN v "go" = 0 := by
      simpa only [locN, hvLoc "go" (by simp), hgoU] using hgo
    have hs := mpt_stopped_local_program v mptInsertFinish haV hgoV
      (fun _ => by rfl) (by decide) (by simp only [hf, Flowing]; trivial)
    rw [hf] at hs
    exact ⟨hs.1, Or.inl hs.2⟩
  · simp only [heq, ↓reduceIte] at hcase
    change evaluateHOLFiniteState s (.dec (ofString "idx") .one
      (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]))
      mptInsertDescent) = (none, u) at hcase
    have hlt : locN s "level" < locN s "klen" := by
      have hne : l.toNat ≠ kl.toNat := fun hh => heq (BitVec.eq_of_toNat_eq hh)
      omega
    obtain ⟨value, d, hv, _, hd, hu⟩ := mpt_dec_none_inv hcase
    obtain ⟨a, i, haE, rfl, hiM⟩ := mpt_loadByte_inv s _ value hv
    obtain ⟨key, l', hkeyE, hlE, haV⟩ := mpt_eval_add2_inv s _ _ (.val (.word a)) haE
    have hl' : l' = l := by
      change s.locals.lookup (ofString "level") = some (.val (.word l')) at hlE
      rw [hl] at hlE
      simpa using hlE.symm
    subst l'
    have haV' : a = key + l := by simpa using haV
    subst a
    have hkeyN := evalAt_local s "key" key hkeyE
    have hstart : key.toNat + l.toNat < 2 ^ 64 := by
      rcases hkey with h0 | ⟨_, _, hinside, _⟩
      · omega
      · have hlim : heapLimit < 2 ^ 64 := by decide
        dsimp only [Inside] at hinside
        omega
    have hsum : (key + l).toNat = key.toNat + l.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hstart]
    have hi : i.toNat < 16 := by
      rcases hkey with h0 | ⟨hnb, _, _, _⟩
      · omega
      · have hx := hnb 0 (by omega)
        rw [hsum] at hiM
        simpa only [Nat.add_zero, ← hlN, ← hkeyN, ← hiM] using hx
    have hnD : NodeHeap (setVarHOLFinite (ofString "idx") (.val (.word i)) s) Nd := hn
    obtain ⟨nn, hnn, hdEq⟩ := mpt_descent_none _ d Nd n l i hnD hm hk hi
      (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hnode)
      (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hl)
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hd
    change nn.toNat = memW s (n.toNat + 32 + 8 * i.toNat) at hnn
    rw [hdEq] at hu
    have huS : u = {s with locals := u.locals} := by rw [hu]; rfl
    have hnodeU := mpt_avoids_none s u mptInsertBranch (ofString "node") (by decide) hb
    have hslotU := mpt_avoids_none s u mptInsertBranch (ofString "slot") (by decide) hb
    have hlevelU := mpt_avoids_none s u mptInsertBranch (ofString "level") (by decide) hb
    have hSU : MptSlotOK u Nd := by
      have hmW : ∀ a, memW u a = memW s a := by intro a; rw [huS]; rfl
      simpa only [MptSlotOK, locN, hnodeU, hslotU, hmW] using hslot
    have hR : u.locals.lookup (ofString "r") = some (.val (.word n)) := by
      rw [hu]
      simp only [lookup_resVarEq_toExact, resVarHOLExact]
      cases hx : s.locals.lookup (ofString "idx") <;>
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          FUPDATE_HOL, FDOMSUB_HOL, ofString]
    have hNN : u.locals.lookup (ofString "next_node") = some (.val (.word nn)) := by
      rw [hu]
      simp only [lookup_resVarEq_toExact, resVarHOLExact]
      cases hx : s.locals.lookup (ofString "idx") <;>
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          FUPDATE_HOL, FDOMSUB_HOL, ofString]
    have hNS : u.locals.lookup (ofString "next_slot") = some (.val (.word (mptChildAddr n i))) := by
      rw [hu]
      simp only [lookup_resVarEq_toExact, resVarHOLExact]
      cases hx : s.locals.lookup (ofString "idx") <;>
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          FUPDATE_HOL, FDOMSUB_HOL, ofString]
    have hNL : u.locals.lookup (ofString "next_level") = some (.val (.word (l + 1#64))) := by
      rw [hu]
      simp only [lookup_resVarEq_toExact, resVarHOLExact]
      cases hx : s.locals.lookup (ofString "idx") <;>
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          FUPDATE_HOL, FDOMSUB_HOL, ofString]
    have hvNode := (hvLoc "node" (by simp)).trans (hnodeU.trans hnode)
    have hvLevel := (hvLoc "level" (by simp)).trans (hlevelU.trans hl)
    have hvSlot : MptSlotOK v Nd := by
      have hmem : ∀ a, memW v a = memW u a := by intro a; rw [hvS]; rfl
      simpa only [MptSlotOK, locN, hvLoc "node" (by simp), hvLoc "slot" (by simp), hmem] using hSU
    obtain ⟨htU, htN, htS, htL⟩ := mpt_finish_none v t Nd n nn (mptChildAddr n i) (l + 1#64)
      hvNode ⟨l, hvLevel⟩
      ((hvLoc "r" (by simp)).trans hR)
      ((hvLoc "next_node" (by simp)).trans hNN)
      ((hvLoc "next_slot" (by simp)).trans hNS)
      ((hvLoc "next_level" (by simp)).trans hNL) hvSlot hf
    have htEq : t = {s with locals := t.locals} := by rw [htU, hvS, huS]
    have htHeap : NodeHeap t Nd := by rw [htEq]; exact hn
    have htKey : ∀ p len, KeyIn t Nd p len ↔ KeyIn s Nd p len := by
      intro p len; rw [htEq]; rfl
    have htLevel : locN t "level" = l.toNat + 1 := by
      have hmax := mpt_locN_lt s "klen"
      simp only [locN, htL, BitVec.toNat_add]
      norm_num
      omega
    have htKlen : locN t "klen" = locN s "klen" := by
      have he := (mpt_avoids_none v t mptInsertFinish (ofString "klen") (by decide) hf).trans
        ((hvLoc "klen" (by simp)).trans (mpt_avoids_none s u mptInsertBranch (ofString "klen") (by decide) hb))
      simp only [locN, he]
    have htVlen : locN t "vlen" = locN s "vlen" := by
      have he := (mpt_avoids_none v t mptInsertFinish (ofString "vlen") (by decide) hf).trans
        ((hvLoc "vlen" (by simp)).trans (mpt_avoids_none s u mptInsertBranch (ofString "vlen") (by decide) hb))
      simp only [locN, he]
    have htKeyLoc : locN t "key" = locN s "key" := by
      have he := (mpt_avoids_none v t mptInsertFinish (ofString "key") (by decide) hf).trans
        ((hvLoc "key" (by simp)).trans (mpt_avoids_none s u mptInsertBranch (ofString "key") (by decide) hb))
      simp only [locN, he]
    refine ⟨⟨?_, fun _ => ⟨?_, Nd, htHeap, ?_, ?_, ?_, ?_, ?_⟩⟩, Or.inr (by omega)⟩
    · rw [htEq]; exact (arenaReady_with_locals s t.locals s.clock).2 ha
    · omega
    · simp only [locN, htN, hnn]
      exact (hn.1 n.toNat hm).2.2.2.2.2.1 hk i.toNat hi
    · rw [htKey, htKeyLoc, htKlen, htLevel]
      have hsuf := mpt_key_suffix s Nd (locN s "key" + locN s "level")
        (locN s "klen" - locN s "level") 1 (by omega) hkey
      convert hsuf using 1 <;> omega
    · right
      refine ⟨n.toNat, hm, Or.inr ⟨?_, i.toNat, hi, ?_⟩, ?_⟩
      · rw [htEq]; exact hk
      · simp only [locN, htS, mpt_child_addr s Nd hn n i hm hk hi]
      · have hmem : ∀ a, memW t a = memW s a := by intro a; rw [htEq]; rfl
        simp only [locN, htN, htS, hmem, mpt_child_addr s Nd hn n i hm hk hi, hnn]
    · simpa only [htVlen] using hvlen
    · simpa only [htKlen] using hklen

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

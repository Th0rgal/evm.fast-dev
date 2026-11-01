import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Split
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Scope

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem lookup_put {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (w : BitVec 64) (x : MlS) :
    (put s n w).locals.lookup x =
      if x = ofString n then some (.val (.word w)) else s.locals.lookup x := by
  simp only [put, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]

theorem locN_put {F : Type} (s : PanSemStateFiniteExact 64 F) (n x : String)
    (w : BitVec 64) :
    locN (put s n w) x = if ofString x = ofString n then w.toNat else locN s x := by
  by_cases he : ofString x = ofString n <;> simp only [locN, lookup_put, he, if_true, if_false]

theorem locN_clock {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) (n : String) :
    locN { s with clock := c } n = locN s n := rfl

theorem memW_put {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (w : BitVec 64) (a : Nat) : memW (put s n w) a = memW s a := rfl

theorem memW_clock {F : Type} (s : PanSemStateFiniteExact 64 F) (c a : Nat) :
    memW { s with clock := c } a = memW s a := rfl

theorem locN_word {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    (hn : locN s n ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)) := by
  unfold locN at hn
  split at hn
  · rename_i w hw
    exact ⟨w, hw⟩
  · exact False.elim (hn rfl)

def descended {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node level sl child : BitVec 64) :=
  put (put (put (put (put s "r" node) "next_node" child)
    "next_slot" (node + 48)) "next_level" (level + sl)) "go" 1

theorem restore_descended {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node level sl child : BitVec 64) (n : String) (old : Option (ValueHOL 64))
    (hne : ofString "r" ≠ ofString n ∧ ofString "next_node" ≠ ofString n ∧
      ofString "next_slot" ≠ ofString n ∧ ofString "next_level" ≠ ofString n ∧
      ofString "go" ≠ ofString n) :
    restore (descended s node level sl child) n old =
      descended (restore s n old) node level sl child := by
  simp only [descended, restore_put_other _ _ _ _ _ hne.1,
    restore_put_other _ _ _ _ _ hne.2.1, restore_put_other _ _ _ _ _ hne.2.2.1,
    restore_put_other _ _ _ _ _ hne.2.2.2.1, restore_put_other _ _ _ _ _ hne.2.2.2.2]

/-- A successful extension branch either stops or performs the exact five descent writes. -/
theorem extension_run (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hnode : locN s "node" ∈ Nd)
    (htag : memW s (locN s "node") = 2)
    (hlev : locN s "level" ≤ locN s "klen")
    (hkey : KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hvlen : locN s "vlen" < 2 ^ 40)
    (hgo : locN s "go" = 0)
    (hr : evaluateHOLFiniteState s extension = (none, t)) :
    ArenaReady t ∧ (locN t "go" = 0 ∨
      ∃ (node level sl child : BitVec 64) (c : Nat),
        s.locals.lookup (ofString "node") = some (.val (.word node)) ∧
        s.locals.lookup (ofString "level") = some (.val (.word level)) ∧
        sl.toNat = memW s (node.toNat + 40) ∧
        child.toNat = memW s (node.toNat + 48) ∧
        sl.toNat ≤ locN s "klen" - locN s "level" ∧
        t = descended { s with clock := c } node level sl child) := by
  have hnonzero : locN s "node" ≠ 0 := by
    have hb := (hn.1 _ hnode).2.2.1.1
    change sourceBase ≤ locN s "node" at hb
    have : 0 < sourceBase := by decide
    omega
  obtain ⟨node, hnv⟩ := locN_word hnonzero
  have hnN : locN s "node" = node.toNat := by simp only [locN, hnv]
  rw [extension_eq] at hr
  obtain ⟨vseg, u0, hvseg, hr0, ht0⟩ := dec_none hr
  obtain ⟨seg, rfl, hseg⟩ := evalAt_loadL s "node" 32 vseg hvseg
  change seg.toNat = memW s (locN s "node" + 32) at hseg
  let s1 := put s "seg" seg
  change evaluateHOLFiniteState s1 _ = _ at hr0
  obtain ⟨vsl, u1, hvsl, hr1, ht1⟩ := dec_none hr0
  obtain ⟨sl, rfl, hsl⟩ := evalAt_loadL s1 "node" 40 vsl hvsl
  have hsl' : sl.toNat = memW s (node.toNat + 40) := by
    simpa +decide [s1, locN_put, hnN, memW_put] using hsl
  let s2 := put s1 "sl" sl
  change evaluateHOLFiniteState s2 _ = _ at hr1
  obtain ⟨values, body, callee, ret, v, post, u2, hargs, hl, he, hcont, ht2⟩ := decCall_none hr1
  have hparams (n : String) (hs : ofString n ≠ ofString "seg")
      (hl : ofString n ≠ ofString "sl") : locN s2 n = locN s n := by
    simp only [s2, s1, locN_put, hs, hl, if_false]
  have hlev2 : locN s2 "level" ≤ locN s2 "klen" := by
    simpa only [hparams "level" (by decide) (by decide),
      hparams "klen" (by decide) (by decide)] using hlev
  obtain ⟨pl, rfl, hplsl, hplkey, hpost⟩ := prefix_return h (s := s2)
    (guestInv_congr (s := s) rfl rfl rfl rfl ha.1) hlev2 hargs hl he
  have hpost' : { post with locals := s2.locals } = { s2 with clock := post.clock } := by
    rw [hpost]
  rw [hpost'] at hcont
  let s3 := put { s2 with clock := post.clock } "pl" pl
  change evaluateHOLFiniteState s3 extDecision = (none, u2) at hcont
  have hlookup (n : String) (hs : ofString n ≠ ofString "seg")
      (hl : ofString n ≠ ofString "sl") (hp : ofString n ≠ ofString "pl") :
      s3.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    simp only [s3, s2, s1, lookup_put, hs, hl, hp, if_false]
  have hparam3 (n : String) (hs : ofString n ≠ ofString "seg")
      (hl : ofString n ≠ ofString "sl") (hp : ofString n ≠ ofString "pl") :
      locN s3 n = locN s n := by simp only [locN, hlookup n hs hl hp]
  have hplsl' : pl.toNat ≤ sl.toNat := by simpa only [s2, locN_put, if_true] using hplsl
  have hplkey' : pl.toNat ≤ locN s "klen" - locN s "level" := by
    simpa only [hparams "klen" (by decide) (by decide),
      hparams "level" (by decide) (by decide)] using hplkey
  have hrestore : t = restore (restore (restore u2 "pl" (s2.locals.lookup (ofString "pl")))
      "sl" (s1.locals.lookup (ofString "sl"))) "seg" (s.locals.lookup (ofString "seg")) := by
    rw [ht0, ht1, ht2]
    rfl
  have harena (hu : ArenaReady u2) : ArenaReady t := by
    rw [hrestore]
    exact restore_arena _ _ (restore_arena _ _ (restore_arena _ _ hu))
  have hago : ArenaReady s3 := localsFree_arenaReady s s3.locals post.clock ha
  rw [extDecision_eq] at hcont
  rcases ite_none hcont with ⟨hmatch, hdesc⟩ | ⟨hdiffer, hsplit⟩
  · obtain ⟨w, hwpl, hwsl⟩ := condTrue_eq hmatch
    have hwpl' : pl = w := by
      simpa only [lv, evalAt, evalHOLExact, s3, lookup_put, if_pos rfl,
        if_true, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using hwpl
    have hwsl' : sl = w := by
      simpa +decide [lv, evalAt, evalHOLExact, s3, s2, lookup_put] using hwsl
    have hpl : pl = sl := hwpl'.trans hwsl'.symm
    clear hwpl' hwsl' hwpl hwsl hmatch
    subst pl
    have hargs' := hargs
    rw [evalListHOLFinite_eq_toExact] at hargs'
    obtain ⟨va, vs1, _, hv1, _⟩ := args_cons hargs'
    obtain ⟨vb, vs2, _, hv2, _⟩ := args_cons hv1
    obtain ⟨vc, vs3, hvc, _, _⟩ := args_cons hv2
    obtain ⟨key, level, _, hlevel, _⟩ := eval_add_locals s2 "key" "level" vc hvc
    have hlevel' : s.locals.lookup (ofString "level") = some (.val (.word level)) := by
      simpa +decide [s2, s1, lookup_put] using hlevel
    obtain ⟨child, hchild, hu2⟩ := descend_run (pl := sl)
      ((hlookup "node" (by decide) (by decide) (by decide)).trans hnv)
      ((hlookup "level" (by decide) (by decide) (by decide)).trans hlevel')
      (by simp only [s3, lookup_put, if_true]) hdesc
    change u2 = descended s3 node level sl child at hu2
    have ht : t = descended { s with clock := post.clock } node level sl child := by
      rw [hrestore, hu2]
      rw [restore_descended _ _ _ _ _ "pl" _ (by decide)]
      change restore (restore (descended
        (restore (put { s2 with clock := post.clock } "pl" sl) "pl"
          (({ s2 with clock := post.clock } : PanSemStateFiniteExact 64 F).locals.lookup (ofString "pl")))
        node level sl child) "sl" _) "seg" _ = _
      rw [restore_put_same, restore_descended _ _ _ _ _ "sl" _ (by decide)]
      change restore (descended (restore (put { s1 with clock := post.clock } "sl" sl)
        "sl" (({ s1 with clock := post.clock } : PanSemStateFiniteExact 64 F).locals.lookup (ofString "sl")))
        node level sl child) "seg" _ = _
      rw [restore_put_same, restore_descended _ _ _ _ _ "seg" _ (by decide)]
      change descended (restore (put { s with clock := post.clock } "seg" seg)
        "seg" (({ s with clock := post.clock } : PanSemStateFiniteExact 64 F).locals.lookup (ofString "seg")))
        node level sl child = _
      rw [restore_put_same]
    refine ⟨?_, Or.inr ⟨node, level, sl, child, post.clock, hnv, hlevel', hsl', hchild, hplkey', ht⟩⟩
    rw [ht]
    exact localsFree_arenaReady s _ post.clock ha
  · have hne : pl ≠ sl := by
      obtain ⟨a, b, ha, hb, hab⟩ := condFalse_eq hdiffer
      have hpa : pl = a := by simpa [lv, evalAt, evalHOLExact, s3, lookup_put] using ha
      have hsb : sl = b := by simpa +decide [lv, evalAt, evalHOLExact, s3, s2, lookup_put] using hb
      exact fun he => hab (hpa.symm.trans (he.trans hsb))
    have hlt : pl.toNat < sl.toNat := by
      have : pl.toNat ≠ sl.toNat := fun he => hne (BitVec.eq_of_toNat_eq he)
      omega
    have hsegkey : KeyIn s Nd seg.toNat pl.toNat := by
      have hp := (hn.1 _ hnode).2.2.2.2.2.2.1 (Or.inr htag)
      have hp' := keyIn_subrange hp (off := 0) (size := pl.toNat) (by
        change 0 + pl.toNat ≤ memW s (locN s "node" + 40)
        rw [hnN, ← hsl']; omega)
      simpa only [Nat.add_zero, ← hseg] using hp'
    have hspl := splitExt_run h (s := s3) (t := u2) hago hn
      (by rw [hparam3 "node" (by decide) (by decide) (by decide)]; exact hnode)
      (by rw [hparam3 "node" (by decide) (by decide) (by decide)]; exact htag)
      (by simpa only [hparam3 "level" (by decide) (by decide) (by decide),
        hparam3 "klen" (by decide) (by decide) (by decide)] using hlev)
      (by rw [hparam3 "key" (by decide) (by decide) (by decide),
        hparam3 "level" (by decide) (by decide) (by decide),
        hparam3 "klen" (by decide) (by decide) (by decide)]; exact hkey)
      (by rw [hparam3 "vlen" (by decide) (by decide) (by decide)]; exact hvlen)
      (by simpa +decide [s3, s2, s1, locN_put, locN_clock, memW_put, memW_clock, hnN, hsl'] using hlt)
      (by simpa +decide [s3, s2, s1, locN_put, locN_clock] using hplkey')
      (by
        have hsegkey3 : KeyIn s3 Nd seg.toNat pl.toNat := hsegkey
        simpa +decide [s3, s2, s1, locN_put, locN_clock] using hsegkey3) hsplit
    refine ⟨harena hspl.1, Or.inl ?_⟩
    rw [hrestore, restore_go _ _ _ (by decide), restore_go _ _ _ (by decide),
      restore_go _ _ _ (by decide), hspl.2,
      hparam3 "go" (by decide) (by decide) (by decide)]
    exact hgo

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2

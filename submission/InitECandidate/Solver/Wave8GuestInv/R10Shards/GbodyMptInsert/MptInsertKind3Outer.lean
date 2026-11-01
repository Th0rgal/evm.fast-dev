import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Tagged

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

theorem mpt_kind3_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (hs : MptInsertActive s) (hk : mptKind s = 3)
    (heval : evaluateHOLFiniteState s mptInsertBody = (none, t)) :
    MptInsertHead t ∧ (locN t "go" = 0 ∨ locN s "level" < locN t "level") := by
  obtain ⟨hle, Nd, hn, hr, hkey, hslot, hvlen, hklen⟩ := hs.1.2 hs.2
  have hne : locN s "node" ≠ 0 := by
    intro hz
    simp only [mptKind, hz, ↓reduceIte] at hk
    contradiction
  have hkind : memW s (locN s "node") = 3 := by simpa only [mptKind, if_neg hne] using hk
  obtain ⟨n, hnode, hnN⟩ := mpt_local_word s "node" hne
  rw [hnN] at hr hkind
  have hm : n.toNat ∈ Nd := hr.resolve_left (by simpa only [← hnN] using hne)
  have hn0 : n ≠ 0 := by intro hz; apply hne; rw [hnN, hz]; rfl
  rw [mptInsert_body_parts] at heval
  obtain ⟨t1, h1, ht1⟩ := mpt_dec_const_none_inv heval
  obtain ⟨t2, h2, ht2⟩ := mpt_dec_const_none_inv h1
  obtain ⟨t3, h3, ht3⟩ := mpt_dec_const_none_inv h2
  obtain ⟨t4, h4, ht4⟩ := mpt_dec_const_none_inv h3
  let entered := setVarHOLFinite (ofString "next_level") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "next_slot") (.val (.word (0#64)))
      (setVarHOLFinite (ofString "next_node") (.val (.word (0#64)))
        (setVarHOLFinite (ofString "r") (.val (.word (0#64))) s)))
  change evaluateHOLFiniteState entered
    (.seq (.assign .local (ofString "go") (.const 0)) (.seq mptInsertDispatch mptInsertFinish)) = (none, t4) at h4
  obtain ⟨g, hassign, hmain⟩ := mpt_seq_none_inv h4
  have hg := mpt_assign_none_word entered g "go" (.const 0) 0 rfl hassign
  subst g
  let start := setVarHOLFinite (ofString "go") (.val (.word (0#64))) entered
  change evaluateHOLFiniteState start (.seq mptInsertDispatch mptInsertFinish) = (none, t4) at hmain
  obtain ⟨beforeFinish, hdispatch, hfinish⟩ := mpt_seq_none_inv hmain
  have hnodeStart : start.locals.lookup (ofString "node") = some (.val (.word n)) := by
    simp (disch := decide) only [start, entered, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, if_neg]
    exact hnode
  rw [mptInsert_dispatch_parts, mpt_ite_eq_local start "node" n 0 _ _ hnodeStart, if_neg hn0] at hdispatch
  obtain ⟨u, hbranch, hrestore⟩ := mpt_tagged_none start beforeFinish Nd n hs.1.1.1.code hn hm hkind hnodeStart hdispatch
  let q := setVarHOLFinite (ofString "k") (.val (.word (3#64))) start
  let c : PanSemStateFiniteExact 64 F := {clearCache q n.toNat with clock := start.clock - 1}
  change evaluateHOLFiniteState c mptInsertBranch = (none, u) at hbranch
  have hqLoc : ∀ name ∈ ["level", "klen", "node", "key", "slot", "vlen"],
      q.locals.lookup (ofString name) = s.locals.lookup (ofString name) := by
    intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [q, start, entered, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, if_neg]
  have hqN : q.locals.lookup (ofString "node") = some (.val (.word n)) :=
    (hqLoc "node" (by simp)).trans hnode
  have hqKey : KeyIn q Nd (locN q "key" + locN q "level") (locN q "klen" - locN q "level") := by
    change KeyIn s Nd _ _
    simpa only [locN, hqLoc "key" (by simp), hqLoc "level" (by simp), hqLoc "klen" (by simp)] using hkey
  have hqSlot : MptSlotOK q Nd := by
    have hmem : ∀ a, memW q a = memW s a := fun _ => rfl
    simpa only [MptSlotOK, locN, hqLoc "slot" (by simp), hqLoc "node" (by simp), hmem] using hslot
  have hcArena : ArenaReady c :=
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hs.1.1.1, hs.1.1.2⟩
  have hcHeap : NodeHeap c Nd :=
    (mpt_nodeHeap_locals (clearCache q n.toNat) (clearCache q n.toNat).locals
      (start.clock - 1) Nd).2 (mpt_clearCache_heap q Nd hn n.toNat hm)
  have hcKind : memW c n.toNat = 3 := by
    have hh := mpt_clearCache_fields q Nd hn n.toNat hm n.toNat hm 0 (Or.inl rfl)
      (lt_of_lt_of_le (by decide : 0 < 32) (mpt_nodeSize_bounds (memW q n.toNat)).1)
    have hclear : memW (clearCache q n.toNat) n.toNat = 3 := by
      simpa only [Nat.add_zero] using hh.trans hkind
    exact (mpt_memW_locals (clearCache q n.toNat) (clearCache q n.toNat).locals
      (start.clock - 1) n.toNat).trans hclear
  have hcLe : locN c "level" ≤ locN c "klen" := by
    change locN q "level" ≤ locN q "klen"
    simpa only [locN, hqLoc "level" (by simp), hqLoc "klen" (by simp)] using hle
  have hcKey : KeyIn c Nd (locN c "key" + locN c "level") (locN c "klen" - locN c "level") :=
    (mpt_keyIn_locals (clearCache q n.toNat) (clearCache q n.toNat).locals
      (start.clock - 1) Nd _ _).2 (mpt_clearCache_key q Nd hn n.toNat hm _ _ hqKey)
  have hcSlot : MptSlotOK c Nd :=
    (mpt_slot_clock (clearCache q n.toNat) (start.clock - 1) Nd).2
      (mpt_clearCache_slot q Nd hn n.toNat hm hqSlot)
  have hcVlen : locN c "vlen" < 2 ^ 40 := by
    change locN q "vlen" < 2 ^ 40
    simpa only [locN, hqLoc "vlen" (by simp)] using hvlen
  have hcKlen : locN c "klen" ≤ 64 := by
    change locN q "klen" ≤ 64
    simpa only [locN, hqLoc "klen" (by simp)] using hklen
  have hcGo : locN c "go" = 0 := by
    change locN q "go" = 0
    simp (disch := decide) only [q, start, entered, locN, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, if_neg, if_pos, BitVec.toNat_ofNat]
  have hvS : beforeFinish = {u with locals := beforeFinish.locals} := by rw [hrestore]; rfl
  have hvLoc : ∀ name ∈ ["go", "node", "slot", "level", "r", "next_node", "next_slot", "next_level", "key", "klen", "vlen"],
      beforeFinish.locals.lookup (ofString name) = u.locals.lookup (ofString name) := by
    intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hrestore, mpt_restore_lookup _ _ _ _ (by decide)]
  obtain ⟨htHead, htEffect⟩ := mpt_branch_finish_none c u beforeFinish t4 Nd n hcArena hcHeap hm hcKind
    hqN hcLe hcKey hcSlot hcVlen hcKlen hcGo hbranch hvS hvLoc hfinish
  have htEq : t = {t4 with locals := t.locals, clock := t4.clock} := by rw [ht1, ht2, ht3, ht4]; rfl
  have htLoc : ∀ name ∈ ["go", "level", "klen", "node", "key", "slot", "vlen"],
      t.locals.lookup (ofString name) = t4.locals.lookup (ofString name) := by
    intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [ht1, ht2, ht3, ht4, mpt_restore_lookup]
  refine ⟨?_, ?_⟩
  · rw [htEq]
    exact mpt_head_locals t4 t.locals t4.clock htLoc htHead
  · have htGo : locN t "go" = locN t4 "go" := by simp only [locN, htLoc "go" (by simp)]
    have htLevel : locN t "level" = locN t4 "level" := by simp only [locN, htLoc "level" (by simp)]
    have hcLevel : locN c "level" = locN s "level" := by
      change locN q "level" = locN s "level"
      simp only [locN, hqLoc "level" (by simp)]
    simpa only [htGo, htLevel, hcLevel] using htEffect

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

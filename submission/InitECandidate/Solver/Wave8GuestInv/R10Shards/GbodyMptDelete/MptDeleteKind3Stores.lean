import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Calls

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
/-- Structural words, separate from the length fields bounded by R10 node typing. -/
def MptStructuralOffset (kind off : Nat) : Prop :=
  off = 0 ∨ ((kind = 1 ∨ kind = 2) ∧ (off = 32 ∨ off = 40)) ∨
    (kind = 2 ∧ off = 48) ∨ (kind = 3 ∧ ∃ i, i < 16 ∧ off = 32 + 8 * i)

theorem mptStructuralOffset_bounds {kind off : Nat} (h : MptStructuralOffset kind off) :
    off + 8 ≤ nodeSize kind ∧ off % 8 = 0 := by
  rcases h with rfl | ⟨hk, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, i, hi, rfl⟩
  all_goals simp only [nodeSize]
  all_goals split_ifs <;> simp_all <;> omega

/-- Preserve structural words, nibble arrays, and the R10 length bounds. -/
theorem mptNodeHeap_fields {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : GuestInv s) (ht : GuestInv t) (hg : AllocatorGrows s t)
    (hn : NodeHeap s Nd)
    (hr : ∀ n ∈ Nd, ∀ off, MptStructuralOffset (memW s n) off →
      memW t (n + off) = memW s (n + off))
    (hkey : ∀ p len, KeyIn s Nd p len → KeyIn t Nd p len)
    (hlength : ∀ n ∈ Nd, memW t (n + 16) < 2 ^ 40 ∧
      (memW s n = 1 → memW t (n + 56) < 2 ^ 40) ∧
      (memW s n = 3 → memW t (n + 168) < 2 ^ 40)) : NodeHeap t Nd := by
  have htag : ∀ n ∈ Nd, memW t n = memW s n := fun n hn => by
    simpa only [Nat.add_zero] using hr n hn 0 (Or.inl rfl)
  have hivl : ∀ n ∈ Nd, nodeIvl t n = nodeIvl s n := fun n hn => by
    simp only [nodeIvl, htag n hn]
  refine ⟨fun n hm => ?_, fun n hnm m hm hne => ?_⟩
  · obtain ⟨hk, hal, hi, hw, hext, hbr, hpath, _⟩ := hn.1 n hm
    rw [htag n hm, hivl n hm]
    refine ⟨hk, hg.allocated hal, hi,
      InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.wordsOK_transfer hs ht hw, ?_, ?_, ?_, hlength n hm⟩
    · intro h2
      rw [hr n hm 48 (Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩)))]
      exact hext h2
    · intro h3 i hi
      have heq := hr n hm (32 + 8 * i) (Or.inr (Or.inr (Or.inr ⟨h3, i, hi, rfl⟩)))
      rw [← Nat.add_assoc] at heq
      rw [heq]
      exact hbr h3 i hi
    · intro h12
      rw [hr n hm 32 (Or.inr (Or.inl ⟨h12, Or.inl rfl⟩)),
        hr n hm 40 (Or.inr (Or.inl ⟨h12, Or.inr rfl⟩))]
      exact hkey _ _ (hpath h12)
  · rw [hivl n hnm, hivl m hm]
    exact hn.2 n hnm m hm hne

/-- The exact state update made by a successful one-word store. -/
def mptWordWrite {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { s with memory := fun b => if b = BitVec.ofNat 64 a then .word w else s.memory b }

theorem mptWordWrite_memW_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : Nat} (w : BitVec 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : b ≠ a) :
    memW (mptWordWrite s a w) b = memW s b := by
  have hbit : BitVec.ofNat 64 b ≠ BitVec.ofNat 64 a := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact hne this
  simp only [mptWordWrite, memW, hbit, if_false]

theorem mptBranchWrite_reads {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) :
    ∀ m ∈ Nd, ∀ k, MptStructuralOffset (memW s m) k →
      memW (mptWordWrite s (n + off) w) (m + k) = memW s (m + k) := by
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have hnhi := (hN.1 n hn).2.2.1.2
  change n + nodeSize (memW s n) ≤ heapLimit at hnhi
  rw [hsize] at hnhi
  have hlim : heapLimit < 2 ^ 64 := by decide
  have ha : n + off < 2 ^ 64 := by rcases hoff with rfl | rfl <;> omega
  intro m hm k hstruct
  obtain ⟨hkb, _⟩ := mptStructuralOffset_bounds hstruct
  have hmhi := (hN.1 m hm).2.2.1.2
  change m + nodeSize (memW s m) ≤ heapLimit at hmhi
  apply mptWordWrite_memW_ne s w ha (by omega)
  by_cases heq : m = n
  · subst m
    rw [hk] at hstruct
    rcases hstruct with hz | ⟨hz, _⟩ | ⟨hz, _⟩ | ⟨_, i, hi, heq⟩
    all_goals rcases hoff with rfl | rfl <;> omega
  · have hd := hN.2 m hm n hn heq
    simp only [Disj, nodeIvl] at hd
    have hmin : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
    rw [hsize] at hd
    rcases hoff with rfl | rfl <;> rcases hd with hd | hd <;> omega

/-- A word write contained in a node record leaves every disjoint key byte
unchanged. The byte interval need not be word aligned. -/
theorem mptWordWrite_key {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {n a : Nat} (hn : n ∈ Nd)
    (ha : n ≤ a ∧ a + 8 ≤ n + nodeSize (memW s n)) (ha64 : a < 2 ^ 64)
    (w : BitVec 64)
    (htag : ∀ m ∈ Nd, memW (mptWordWrite s a w) m = memW s m)
    {p len : Nat} (hk : KeyIn s Nd p len) : KeyIn (mptWordWrite s a w) Nd p len := by
  rcases hk with hz | ⟨hnib, hal, hi, hd⟩
  · exact Or.inl hz
  · right
    refine ⟨?_, hal, hi, ?_⟩
    · intro k hk
      have hu : InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.IvlUnhit s
          (mptWordWrite s a w) (p, len) := by
        intro b _ hb
        have hne : b ≠ BitVec.ofNat 64 a := by
          intro heq
          subst b
          have hnat : (BitVec.ofNat 64 a).toNat = a := by
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
          rw [hnat] at hb
          have hdisj := hd n hn
          simp only [Disj, nodeIvl] at hdisj
          change p < a + 8 ∧ a < p + len at hb
          rcases hdisj with hdisj | hdisj <;> omega
        simp only [mptWordWrite, hne, if_false]
      rw [InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.memB_eq_of_ivlUnhit hu rfl (by
        have := hi.2
        have hlim : heapLimit ≤ 2 ^ 64 := by decide
        omega) ⟨by omega, by omega⟩]
      exact hnib k hk
    · intro m hm
      simpa only [nodeIvl, htag m hm] using hd m hm

theorem mptWordWrite_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Nat) (w : BitVec 64) {bound : Nat}
    (hw : w.toNat < bound) (hb : memW s b < bound) :
    memW (mptWordWrite s a w) b < bound := by
  simp only [mptWordWrite, memW]
  split
  · exact hw
  · exact hb

theorem mptBranchWrite_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : GuestInv s) (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40) :
    NodeHeap (mptWordWrite s (n + off) w) Nd ∧
      (∀ p len, KeyIn s Nd p len → KeyIn (mptWordWrite s (n + off) w) Nd p len) := by
  have hr := mptBranchWrite_reads hN hn hk hoff w
  have htag : ∀ m ∈ Nd, memW (mptWordWrite s (n + off) w) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using hr m hm 0 (Or.inl rfl)
  have hbound : n + nodeSize (memW s n) ≤ heapLimit := (hN.1 n hn).2.2.1.2
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have ha : n ≤ n + off ∧ n + off + 8 ≤ n + nodeSize (memW s n) := by
    rcases hoff with rfl | rfl <;> rw [hsize] <;> constructor <;> omega
  have ha64 : n + off < 2 ^ 64 := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  have hkey : ∀ p len, KeyIn s Nd p len → KeyIn (mptWordWrite s (n + off) w) Nd p len :=
    fun _ _ hk => mptWordWrite_key hn ha ha64 w htag hk
  refine ⟨mptNodeHeap_fields hs ?_ ⟨Nat.le_refl _, Nat.le_refl _⟩ hN hr hkey ?_, hkey⟩
  · exact guestInv_congr (s := s) rfl rfl rfl rfl hs
  intro m hm
  obtain ⟨_, _, _, _, _, _, _, hcache, hleaf, hbranch⟩ := hN.1 m hm
  exact ⟨mptWordWrite_lt s _ _ w hw hcache,
    fun h1 => mptWordWrite_lt s _ _ w hw (hleaf h1),
    fun h3 => mptWordWrite_lt s _ _ w hw (hbranch h3)⟩

theorem mptBranchWrite_stack {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40)
    {fs : List Nat} {p : Nat} (hst : MptStack s Nd p fs) :
    MptStack (mptWordWrite s (n + off) w) Nd p fs := by
  have ht : GuestInv (mptWordWrite s (n + off) w) :=
    guestInv_congr (s := s) rfl rfl rfl rfl hs.1
  obtain ⟨_, hkey⟩ := mptBranchWrite_heap hs.1 hN hn hk hoff w hw
  have hr := mptBranchWrite_reads hN hn hk hoff w
  have hkind : ∀ m ∈ Nd, memW (mptWordWrite s (n + off) w) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using hr m hm 0 (Or.inl rfl)
  apply mptStack_transfer hs.1 ht ⟨Nat.le_refl _, Nat.le_refl _⟩
    (fun _ hm => hm) hkind hkey ?_ fs p hst
  intro a hlo hhi _
  have hbound := (hN.1 n hn).2.2.1.2
  change n + nodeSize (memW s n) ≤ heapLimit at hbound
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have ⟨_, _, hflo, hgap, _, _, _, _⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hlim : scratchEnd < 2 ^ 64 := by decide
  apply mptWordWrite_memW_ne s w
  · rcases hoff with rfl | rfl <;> rw [hsize] at hbound <;> omega
  · omega
  · rcases hoff with rfl | rfl <;> rw [hsize] at hbound <;> omega

theorem mptDeleteBranch_write {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) {off : Nat} (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40) :
    MptDeleteBranchReady (mptWordWrite s (locN s "node" + off) w) := by
  obtain ⟨ha, hgo, htag, Nd, fs, hn, hstack, hres, hlevel, hnode, hkey⟩ := hs
  obtain ⟨hnt, hkeys⟩ := mptBranchWrite_heap ha.1 hn hnode.1 hnode.2 hoff w hw
  refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl ha.1, ha.2⟩,
    hgo, htag, Nd, fs, hnt, ?_, hres, hlevel, ?_, hkeys _ _ hkey⟩
  · exact mptBranchWrite_stack ha hn hnode.1 hnode.2 hoff w hw hstack
  · refine ⟨hnode.1, ?_⟩
    have heq := mptBranchWrite_reads hn hnode.1 hnode.2 hoff w _ hnode.1 0 (Or.inl rfl)
    change memW (mptWordWrite s (locN s "node" + off) w) (locN s "node") = 3
    simpa only [Nat.add_zero, hnode.2] using heq

theorem mptLocN_nonzero {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    (hn : locN s n ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)) ∧ w.toNat = locN s n := by
  unfold locN at hn ⊢
  split at hn
  · rename_i w hw
    exact ⟨w, hw, rfl⟩
  · contradiction

theorem mptStore_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : ExpHOL 64) (a w : BitVec 64)
    (hd : evalAt s dst = some (.val (.word a)))
    (hv : evalAt s src = some (.val (.word w))) (ha : s.memaddrs a) :
    evaluateHOLFiniteState s (.store dst src) =
      (none, { s with memory := fun b => if b = a then .word w else s.memory b }) := by
  rw [evaluateHOLFiniteState_store]
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst = _ at hd
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = _ at hv
  rw [hd, hv]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, ha, if_true]

theorem mptDeleteBranch_store_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) {off : Nat} (hoff : off = 160 ∨ off = 168) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 off)]) (.const 0)) =
      (none, mptWordWrite s (locN s "node" + off) 0) := by
  obtain ⟨ha, _, _, Nd, fs, hN, _, _, _, hnode, _⟩ := hs
  obtain ⟨_, _, hinside, hw, _⟩ := hN.1 _ hnode.1
  have hsize : nodeSize (memW s (locN s "node")) = 176 := by simp [nodeSize, hnode.2]
  change sourceBase ≤ locN s "node" ∧
    locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hinside
  change locN s "node" % 8 = 0 ∧ _ at hw
  rw [hsize] at hinside
  have hnonnull : locN s "node" ≠ 0 := by
    have hbase : 0 < sourceBase := by decide
    omega
  obtain ⟨nw, hnw, hnat⟩ := mptLocN_nonzero hnonnull
  have hoff64 : off < 2 ^ 64 := by rcases hoff with rfl | rfl <;> decide
  have hadd : nw + BitVec.ofNat 64 off = BitVec.ofNat 64 (locN s "node" + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, hnat]
  apply mptStore_eval s _ _ (BitVec.ofNat 64 (locN s "node" + off)) 0
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ = _
    simp [evalHOLExact, evalListHOLExact, hnw, valueIsWord, valueWord, wordOpHOL, wordOp, hadd]
  · rfl
  · obtain ⟨_, hdom, _⟩ := InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.wordAt_of_ordinary ha.1
      (a := locN s "node" + off)
      (by rcases hoff with rfl | rfl <;> omega)
      (by omega)
      (by have hlim : heapLimit ≤ heapEnd := by decide
          rcases hoff with rfl | rfl <;> omega)
    exact hdom

theorem mptDeleteBranch_store (off : Nat) (hoff : off = 160 ∨ off = 168) :
    Hoare MptDeleteBranchReady
      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 off)]) (.const 0))
      (fun r t => r = none → MptDeleteBranchReady t) := by
  refine ⟨fun s _ hs _ _ => ?_⟩
  rw [mptDeleteBranch_store_eval hs hoff]
  exact mptDeleteBranch_write hs hoff 0 (by decide)

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete

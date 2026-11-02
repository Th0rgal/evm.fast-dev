import InitECandidate.Solver.Wave8GuestInv.Bounds

/-! Provisional R10 definition-only view. See R10_SURGEON_BRIEF.md and the shard manifest.
No R9 contract theorem is assumed by importing this module. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def memW {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  match s.memory (BitVec.ofNat 64 a) with
  | .word w => w.toNat

def WordAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Prop :=
  ∃ w : BitVec 64, s.memaddrs (BitVec.ofNat 64 a) ∧ s.memory (BitVec.ofNat 64 a) = .word w

def globN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.globals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

def locN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.locals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

abbrev Ivl := Nat × Nat

def Inside (i : Ivl) (lo hi : Nat) : Prop := lo ≤ i.1 ∧ i.1 + i.2 ≤ hi

def Disj (i j : Ivl) : Prop := i.2 = 0 ∨ j.2 = 0 ∨ i.1 + i.2 ≤ j.1 ∨ j.1 + j.2 ≤ i.1

def InIvl (a : Nat) (i : Ivl) : Prop := i.1 ≤ a ∧ a < i.1 + i.2

def WordsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  i.1 % 8 = 0 ∧ i.2 % 8 = 0 ∧ ∀ k, k < i.2 / 8 → WordAt s (i.1 + 8 * k)

def ArenaOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  sourceBase ≤ globN s "heap_ptr" ∧ globN s "heap_ptr" ≤ heapLimit ∧
  scratchStart ≤ globN s "frame_mem_ptr" ∧ globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" ∧
  globN s "scratch_ptr" ≤ scratchEnd ∧
  globN s "heap_ptr" % 8 = 0 ∧ globN s "frame_mem_ptr" % 8 = 0 ∧ globN s "scratch_ptr" % 8 = 0

def ArenaReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ArenaOK s

def Allocated {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  Inside i sourceBase (globN s "heap_ptr") ∨ Inside i (globN s "scratch_ptr") scratchEnd

def AllocatorGrows {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr"

def hdr {F : Type} (s : PanSemStateFiniteExact 64 F) (t k : Nat) : Nat := memW s (t + 8 * k)

def nodeF {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes n off : Nat) : Nat :=
  memW s (nodes + 32 * n + off)

def htabFootprint {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : List Ivl :=
  [(t, 88), (hdr s t 4, (hdr s t 10 + 1) * hdr s t 1), (hdr s t 5, (hdr s t 10 + 1) * 32),
   (hdr s t 6, (hdr s t 10 + 1) * 8)]

def FreeChain {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) : Nat → List Nat → Prop
  | head, [] => head = 0
  | head, f :: rest => head = f ∧ FreeChain s nodes (nodeF s nodes f 0) rest

def HtabWF {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : Prop :=
  let klen := hdr s t 0
  let cnt := hdr s t 3
  let nodes := hdr s t 5
  let order := hdr s t 6
  let root := hdr s t 7
  let next := hdr s t 8
  let ncap := hdr s t 10
  let nd := nodeF s nodes
  (∀ i ∈ htabFootprint s t, Inside i sourceBase heapEnd ∧ WordsOK s i) ∧
  (htabFootprint s t).Pairwise Disj ∧
  1 ≤ klen ∧ klen ≤ maxKeyLen ∧ hdr s t 1 = (klen + 7) / 8 * 8 ∧
  2 ≤ ncap ∧ 1 ≤ next ∧ next ≤ ncap + 1 ∧
  ∃ L I Fr : List Nat,
    L.length = cnt ∧ (L ++ I ++ Fr).Nodup ∧
    (∀ n, n ∈ L ++ I ++ Fr ↔ 1 ≤ n ∧ n < next) ∧
    ((cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt) ∧
    (∀ (i : Nat) (h : i < L.length),
      memW s (order + 8 * i) = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i) ∧
    (∀ n ∈ I, nd n 24 < 8 * klen ∧ nd n 8 ∈ L ++ I ∧ nd n 16 ∈ L ++ I ∧ nd n 8 ≠ nd n 16 ∧
      nd (nd n 8) 0 = n ∧ nd (nd n 16) 0 = n) ∧
    (cnt = 0 → root = 0) ∧ (0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0) ∧
    (∀ n ∈ I, nd n 8 ≠ root ∧ nd n 16 ≠ root) ∧
    (∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I) ∧
    (∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root →
      (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧ dep (nd n 0) < dep n) ∧
    FreeChain s nodes (hdr s t 9) Fr

def HtabValuesIn {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) (S : List Nat) : Prop :=
  ∀ i, i < hdr s t 3 → nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8 ∈ S

def CellHits (a : Nat) (i : Ivl) : Prop := i.1 < a + 8 ∧ a < i.1 + i.2

def FrameOutside {F : Type} (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl)
    (fresh : Ivl) : Prop :=
  ∀ a : BitVec 64, (∀ i ∈ keep, ¬ CellHits a.toNat i) → ¬ CellHits a.toNat fresh →
    post.memory a = s.memory a


example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b } [] (x.toNat, 8) := by
  intro a _ hout
  have hne : a ≠ x := by
    rintro rfl
    exact hout ⟨by omega, by omega⟩
  simp [hne]



example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b }
      [(x.toNat + 1, 1)] (0, 0) := by
  intro a hkeep _
  have hne : a ≠ x := by
    rintro rfl
    exact hkeep _ (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
  simp [hne]

def FunEnsures (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      ∀ v, (evaluateHOLFiniteState s body).1 = some (.returned v) →
        Q s (evaluateHOLFiniteState s body).2

def HtabArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "t") ∧
    ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i

def HtabExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "t"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k)

def UnionArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "dst") ∧
    ∀ i ∈ htabFootprint s (locN s "dst"), Allocated s i

def UnionExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "dst"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k)

def wsTableSlots : List Nat := [32]

def bsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 72]

def tsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 56, 64]

def globalTableRoots : List String := ["bal_accounts", "bal_idx_accts", "bal_idx_stor"]

def globalBuffers : List (String × Nat) :=
  [("b2_iv", 64), ("b2_sigma", 80), ("b2_v", 128), ("bal_key_buf", 64), ("be", 120), ("beacon_roots_address", 24), ("bls_c", 7136), ("bls_discount", 2048), ("bn_expw", 352), ("bn_gamma", 384), ("bo", 88), ("bs", 80), ("builder_deposit_address", 24), ("builder_exit_address", 24), ("consolidation_request_address", 24), ("deposit_contract_address", 24), ("deposit_event_signature_hash", 32), ("empty_code_hash", 32), ("empty_trie_root", 32), ("evm_empty", 8), ("evm_key_buf", 32), ("hdr_zero8", 8), ("history_storage_address", 24), ("keccak_pad", 136), ("keccak_rc", 192), ("keccak_st", 200), ("mpt_hash_scratch", 40), ("mpt_key_scratch", 16), ("mpt_nib_scratch", 64), ("null_address", 24), ("pre_hdr_buf", 96), ("precompile_addrs", 360), ("rmd_h", 40), ("rmd_pad", 128), ("rmd_tab", 160), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64), ("sk_buf", 64), ("ssz_len_chunk", 32), ("ssz_offs", 64), ("transfer_topic", 32), ("ts", 72), ("u256_ws", 640), ("vm_system_address", 24), ("withdrawal_request_address", 24), ("ws", 40), ("zero32", 32), ("zero_hashes", 2048)]

def blockOutObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (let bo := globN s "bo"
  let obj (p len : Nat) : Ivl := if bo = 0 ∨ p = 0 then (0, 0) else (p, len)
  let lst (k : Nat) : List Ivl :=
    [obj (memW s (bo + k)) 24, obj (memW s (memW s (bo + k))) (8 * memW s (memW s (bo + k) + 16))]
  [obj (memW s (bo + 24)) (16 * memW s (bo + 80) + 16), obj (memW s (bo + 32)) (16 * memW s (bo + 80) + 16),
   obj (memW s (bo + 56)) 128] ++ lst 40 ++ lst 72).map (fun i => if i.2 = 0 then (0, 0) else i)

def lstObjects {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) : List Ivl :=
  ([(l, 24), (memW s l, esz * memW s (l + 16))]).map (fun i => if i.2 = 0 then (0, 0) else i)

def LstOK {F : Type} (s : PanSemStateFiniteExact 64 F) (l : Nat) : Prop :=
  1 ≤ memW s (l + 16) ∧ memW s (l + 8) ≤ memW s (l + 16)

def htabValues {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : List Nat :=
  (List.range (hdr s t 3)).map fun i => nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8

def balRecords {F : Type} (s : PanSemStateFiniteExact 64 F) : List Nat :=
  let t := globN s "bal_accounts"
  if t = 0 then [] else
    (List.range (hdr s t 3)).map fun i => nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8

def balObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  ((balRecords s).flatMap fun ad =>
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++ lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap fun l => lstObjects s l 40).map (fun i => if i.2 = 0 then (0, 0) else i)

def fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  ((globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
    [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s).map (fun i => if i.2 = 0 then (0, 0) else i)

def RootIn (S : List Nat) (v : Nat) : Prop := v = 0 ∨ v ∈ S

def tableRoles : List (String × Nat) :=
  [("ws+16", 32), ("ws+32", 32), ("bs+8", 20), ("bs+16", 20), ("bs+24", 52), ("bs+32", 20), ("bs+40", 52),
   ("bs+48", 32), ("bs+72", 20), ("ts+8", 20), ("ts+16", 20), ("ts+24", 52), ("ts+32", 20),
   ("ts+40", 52), ("ts+48", 32), ("ts+56", 20), ("ts+64", 52), ("bal_accounts", 20),
   ("bal_idx_accts", 28), ("bal_idx_stor", 60), ("bs.inner", 32), ("ts.inner", 32),
   ("bal.stor", 32), ("bal.reads", 32), ("frame.del", 20), ("frame.addr", 20), ("frame.key", 52)]

def roleKeyLen (r : String) : Nat := (tableRoles.lookup r).getD 0

def sharedRoles : List String := ["bs.inner", "ts.inner", "frame.del", "frame.addr", "frame.key"]

def recRoles {F : Type} (s : PanSemStateFiniteExact 64 F) (g : String) (ks : List (Nat × String)) :
    List (Nat × String) :=
  if globN s g = 0 then [] else ks.map fun k => (memW s (globN s g + k.1), k.2)

def nestRoles {F : Type} (s : PanSemStateFiniteExact 64 F) (g r : String) : List (Nat × String) :=
  if globN s g = 0 then [] else if memW s (globN s g + 32) = 0 then [] else
    (htabValues s (memW s (globN s g + 32))).map fun v => (v, r)

def worldRoleSlots {F : Type} (s : PanSemStateFiniteExact 64 F) : List (Nat × String) :=
  (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
    recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
      (48, "bs+48"), (72, "bs+72")] ++
    recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
      (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
    [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
      (globN s "bal_idx_stor", "bal_idx_stor")] ++
    nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner" ++
    (balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]).filter
    fun a => a.1 != 0

def journalRole {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : String :=
  if globN s "ts" ≠ 0 ∧ t = memW s (globN s "ts" + 16) then "ts+16"
  else if globN s "ts" ≠ 0 ∧ t = memW s (globN s "ts" + 32) then "ts+32"
  else if globN s "ts" ≠ 0 ∧ t = memW s (globN s "ts" + 48) then "ts+48"
  else if globN s "ts" ≠ 0 ∧ t = memW s (globN s "ts" + 64) then "ts+64"
  else "ts.inner"

def journalRoleSlots {F : Type} (s : PanSemStateFiniteExact 64 F) : List (Nat × String) :=
  (List.range (globN s "journal_n")).flatMap fun i =>
    let j := globN s "journal" + 32 * i
    (memW s j, journalRole s (memW s j)) ::
      (if memW s (j + 16) ≠ 0 ∧ journalRole s (memW s j) = "ts+32" then
        [(memW s (j + 24), "ts.inner")] else [])

def RolesOK {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (sl jr : List (Nat × String)) : Prop :=
  (∀ a ∈ sl ++ jr, a.1 ∈ S ∧ hdr s a.1 0 = roleKeyLen a.2) ∧
  sl.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) ∧
  ∀ a ∈ jr, ∀ b ∈ sl ++ jr, a.1 = b.1 → a.2 = b.2

def TablesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  S.Nodup ∧
  (∀ t ∈ S, HtabWF s t ∧ ∀ i ∈ htabFootprint s t, Allocated s i ∧
    ∀ j ∈ fixedObjects s, Disj i j) ∧
  (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ∀ i ∈ htabFootprint s t, ∀ j ∈ htabFootprint s u, Disj i j) ∧
  (∀ k ∈ wsTableSlots, globN s "ws" ≠ 0 → RootIn S (memW s (globN s "ws" + k))) ∧
  (∀ k ∈ bsTableSlots, globN s "bs" ≠ 0 → RootIn S (memW s (globN s "bs" + k))) ∧
  (∀ k ∈ tsTableSlots, globN s "ts" ≠ 0 → RootIn S (memW s (globN s "ts" + k))) ∧
  (∀ g ∈ globalTableRoots, RootIn S (globN s g)) ∧
  (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ∈ S → HtabValuesIn s (memW s (globN s "bs" + 32)) S) ∧
  (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ∈ S → HtabValuesIn s (memW s (globN s "ts" + 32)) S) ∧
  (∀ ad ∈ balRecords s, memW s ad ∈ S ∧ memW s (ad + 8) ∈ S ∧
    (∀ k ∈ [16, 24, 32], LstOK s (memW s (ad + k))) ∧
    ∀ l ∈ htabValues s (memW s ad), LstOK s l) ∧
  (globN s "bo" ≠ 0 → ∀ k ∈ [40, 72], memW s (globN s "bo" + k) ≠ 0 → LstOK s (memW s (globN s "bo" + k))) ∧
  RolesOK s S (worldRoleSlots s) (journalRoleSlots s)

def JournalTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  globN s "journal_n" ≤ globN s "journal_cap" ∧ globN s "journal_cap" ≤ journalCapMax ∧
  (globN s "journal_cap" = 0 ∨ (Allocated s (globN s "journal", 32 * globN s "journal_cap") ∧
    WordsOK s (globN s "journal", 32 * globN s "journal_cap"))) ∧
  ∀ i, i < globN s "journal_n" → memW s (globN s "journal" + 32 * i) ∈ S

def FixedTyped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ i ∈ fixedObjects s, i.2 = 0 ∨ (Allocated s i ∧ WordsOK s i)) ∧ (fixedObjects s).Pairwise Disj

def nodeSize (kind : Nat) : Nat :=
  if kind = 0 then 32 else if kind = 1 then 64 else if kind = 2 then 56 else 176

def nodeIvl {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Ivl := (n, nodeSize (memW s n))

def memB {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  match s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat

def NibblesOK {F : Type} (s : PanSemStateFiniteExact 64 F) (p len : Nat) : Prop :=
  ∀ k, k < len → memB s (p + k) < 16

def KeyIn {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (p len : Nat) : Prop :=
  len = 0 ∨ (NibblesOK s p len ∧ Allocated s (p, len) ∧ Inside (p, len) sourceBase heapLimit ∧
    ∀ n ∈ Nd, Disj (p, len) (nodeIvl s n))

def nodePath {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Ivl :=
  if (memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0 then (memW s (n + 32), memW s (n + 40))
  else (0, 0)

def NodeHeap {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  (∀ n ∈ Nd, memW s n ≤ 3 ∧
    (memW s n = 1 → memW s (n + 56) < 2 ^ 40) ∧
    (memW s n = 3 → memW s (n + 168) < 2 ^ 40) ∧ Allocated s (nodeIvl s n) ∧ Inside (nodeIvl s n) sourceBase heapLimit ∧
    WordsOK s (nodeIvl s n) ∧
    (memW s n = 2 → RootIn Nd (memW s (n + 48))) ∧
    (memW s n = 3 → ∀ i, i < 16 → RootIn Nd (memW s (n + 32 + 8 * i))) ∧
    ((memW s n = 1 ∨ memW s n = 2) → KeyIn s Nd (memW s (n + 32)) (memW s (n + 40)))) ∧
  (∀ n ∈ Nd, ∀ m ∈ Nd, n ≠ m → Disj (nodeIvl s n) (nodeIvl s m))

def nodeExtents {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : List Ivl :=
  Nd.flatMap fun n => [nodeIvl s n, nodePath s n]

def TriesTypedWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  NodeHeap s Nd ∧
    (∀ o ∈ nodeExtents s Nd, (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j) ∧
    (globN s "ws" ≠ 0 → RootIn Nd (memW s (globN s "ws" + 24)) ∧
      (memW s (globN s "ws" + 32) ∈ S → ∀ i, i < hdr s (memW s (globN s "ws" + 32)) 3 →
        RootIn Nd (nodeF s (hdr s (memW s (globN s "ws" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 - 1)))

def TriesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nd : List Nat, TriesTypedWith s S Nd

def AvoidsTries {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (os : List Ivl) :
    Prop :=
  ∃ Nd : List Nat, TriesTypedWith s S Nd ∧ ∀ o ∈ os, ∀ j ∈ nodeExtents s Nd, Disj o j

def WorldTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTyped s S

def WorldOK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S

def evmChainFrom {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat → Nat → Nat → List Ivl
  | 0, _, _ => []
  | fuel + 1, e, c =>
    (e, c) :: (if memW s (c + 16) = 0 then [] else evmChainFrom s fuel (memW s c) (memW s (c + 8)))

def evmChain {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  evmChainFrom s (maxChain + 1) (globN s "ev") (globN s "cur_cont")

abbrev EvmDone {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "cur_cont" + 32) ≠ 0 ∨ memW s (globN s "ev" + 104) = 0 ∨
    memW s (globN s "ev" + 56) ≤ memW s (globN s "ev")

def frameLogs {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 16))

def frameRet {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  if memW s (ec.1 + 216) = 0 then (0, 0)
  else (memW s (ec.1 + 144), (memW s (ec.1 + 216) + 15) / 8 * 8)

def frameObjects {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 24), memW s (ec.1 + 40)), (memW s (ec.1 + 88), 24), frameLogs s ec,
   frameRet s ec]

def frameScratch {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 88), 24)]

def FrameWF {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ec : Ivl) : Prop :=
  let e := ec.1
  (∀ i ∈ [(e, 280), (ec.2, 104), (memW s (e + 8), 32 * memW s (e + 232)), (memW s (e + 88), 24)],
    Inside i (globN s "scratch_ptr") scratchEnd ∧ WordsOK s i) ∧
  Inside (memW s (e + 24), memW s (e + 40)) scratchStart (globN s "frame_mem_ptr") ∧
  WordsOK s (memW s (e + 24), memW s (e + 40)) ∧
  1 ≤ memW s (e + 232) ∧ memW s (e + 16) ≤ memW s (e + 232) ∧ memW s (e + 232) ≤ 1024 ∧
  memW s (e + 32) ≤ memW s (e + 40) ∧
  memW s (e + 136) ∈ S ∧ memW s (e + 168) ∈ S ∧ memW s (e + 176) ∈ S ∧
  1 ≤ memW s (memW s (e + 88) + 16) ∧
  memW s (memW s (e + 88) + 8) ≤ memW s (memW s (e + 88) + 16) ∧
  (Inside (frameLogs s ec) sourceBase (globN s "heap_ptr") ∨
    Inside (frameLogs s ec) (globN s "scratch_ptr") scratchEnd) ∧
  WordsOK s (frameLogs s ec) ∧
  ((memW s (e + 216) = 0 ∧ memW s (e + 144) = globN s "evm_empty") ∨
    (Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK s (frameRet s ec)))

def FrameRoom {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Prop :=
  memW s (ec.1 + 16) + 1 ≤ memW s (ec.1 + 232)

def RetWindowsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    memW s ((ch[i]'(by omega)).2 + 80) = 0 ∨
      memW s ((ch[i]'(by omega)).2 + 72) + memW s ((ch[i]'(by omega)).2 + 80) ≤
        memW s (ch[i + 1].1 + 40)

def recordSlots {F : Type} (s : PanSemStateFiniteExact 64 F) (g : String) (ks : List Nat) :
    List Nat :=
  if globN s g = 0 then [] else ks.map fun k => memW s (globN s g + k)

def worldTableRefs {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : List Nat :=
  let nest (g : String) : List Nat :=
    if globN s g ≠ 0 ∧ memW s (globN s g + 32) ∈ S then htabValues s (memW s (globN s g + 32))
    else []
  recordSlots s "ws" wsTableSlots ++ recordSlots s "bs" bsTableSlots ++
    recordSlots s "ts" tsTableSlots ++ globalTableRoots.map (globN s) ++ nest "bs" ++ nest "ts" ++
    (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) ++
    (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k))

def DelExclusive {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ch : List Ivl)
    (i t : Nat) : Prop :=
  t ∉ worldTableRefs s S ∧
  ∀ (j : Nat) (hj : j < ch.length), ∀ k ∈ [136, 168, 176], memW s (ch[j].1 + k) = t → k = 136 ∧ j ≤ i

def MarksOK {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    let m := memW s ((ch[i]'(by omega)).2 + 48)
    let mm := memW s ((ch[i]'(by omega)).2 + 56)
    m ≤ scratchEnd ∧ scratchStart ≤ mm ∧ m % 8 = 0 ∧ mm % 8 = 0 ∧
    (∀ j (hj : j < ch.length), i < j →
      (∀ o ∈ frameScratch s ch[j], Inside o m scratchEnd) ∧
      Inside (frameObjects s ch[j])[3]! scratchStart mm ∧
      (Inside (frameLogs s ch[j]) sourceBase heapLimit ∨ Inside (frameLogs s ch[j]) m scratchEnd)) ∧
    (∀ o ∈ frameScratch s (ch[i]'(by omega)), o.1 + o.2 ≤ m) ∧
    mm ≤ memW s ((ch[i]'(by omega)).1 + 24) ∧
    (∀ t ∈ S, (t ∈ (ch.take (i + 1)).map (fun ec => memW s (ec.1 + 136)) ∧ DelExclusive s S ch i t) ∨
      ∀ o ∈ htabFootprint s t, Inside o sourceBase heapLimit ∨ Inside o m scratchEnd) ∧
    (∀ o ∈ fixedObjects s, o.2 = 0 ∨ Inside o sourceBase heapLimit ∨ Inside o m scratchEnd)

def frameRoleSlots {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) :
    List (Nat × String) :=
  ch.flatMap fun ec => [(memW s (ec.1 + 136), "frame.del"), (memW s (ec.1 + 168), "frame.addr"),
    (memW s (ec.1 + 176), "frame.key")]

def EvmInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s) ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

def evmPotS : Nat := maxChain * 2 ^ 64

def evmPotF : Nat := 2 * maxChain + 2

def evmPot {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  let ch := evmChain s
  let R := (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum
  let Fp := 2 * ch.length + (if EvmDone s then 0 else 1)
  let S := (ch.map fun ec => memW s (ec.1 + 72)).sum
  R * (evmPotF * evmPotS) + Fp * evmPotS + S

def evmPotMax : Nat := (2 * maxChain * 2 ^ 64 + 1) * evmPotF * evmPotS

def runFramesLoop : Option (ExpHOL 64 × ProgHOL 64) :=
  match originalRuntimeCode.lookup (ofString "run_frames") with
  | some (_, .dec _ _ _ (.seq (.while c b) _), _) => some (c, b)
  | _ => none

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, s.locals, retShape)) →
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
    ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"]).map ofString → s.globals.lookup k = post.globals.lookup k

def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

def MptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧ ∃ Nd, NodeHeap s Nd ∧
    RootIn Nd (locN s "node") ∧
    KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

def MptObjInWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nm : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 16) ∧ WordsOK s (m, 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 16) j) ∧
  NodeHeap s Nm ∧ RootIn Nm (memW s m) ∧
    ∀ o ∈ nodeExtents s Nm, Disj o (m, 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j

def MptObjIn {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nm, MptObjInWith s S Nm (locN s "m")

def MptObjAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ MptObjIn s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S ((locN s "m", 16) :: R s) ∧
    ∃ Nm Nd, MptObjInWith s S Nm (locN s "m") ∧ TriesTypedWith s S Nd ∧
      ∀ o ∈ (locN s "m", 16) :: R s ++ nodeExtents s Nm, ∀ j ∈ nodeExtents s Nd, Disj o j

def MptObjReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptObjAvoids (fun _ => []) s

def MptExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"]).map ofString → s.globals.lookup k = post.globals.lookup k) ∧
    ∃ Nd Nd', NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ NodeHeap post Nd' ∧
      RootIn Nd' w.toNat ∧
      FrameOutside s post
        ((Nd.map fun n => nodeIvl s n) ++
          [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

def IsEvmErr (r : Option (PanSemResultExact 64)) : Prop :=
  ∃ v, r = some (.exception (ofString "EvmErr") v)

def EvmRun : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ¬ EvmDone s

def FinishReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

def RollbackReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) : Prop :=
  ArenaReady s ∧ Allocated s (c, 280) ∧ WordsOK s (c, 280) ∧
    (∀ k ∈ [168, 176],
      HtabWF s (memW s (c + k)) ∧
      ∀ i ∈ htabFootprint s (memW s (c + k)), Allocated s i ∧ Disj (c, 280) i) ∧
    (memW s (c + 168) = memW s (c + 176) ∨
      ∀ i ∈ htabFootprint s (memW s (c + 168)), ∀ j ∈ htabFootprint s (memW s (c + 176)), Disj i j)

def RollbackReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RollbackReadyAt s (locN s "child")

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

def KeepsOn (P W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun _ r post => Resumes r → W post) fname

def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ (gw).map ofString → s.globals.lookup k = post.globals.lookup k)
    fname

def WorldAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S (R s)

def TxReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 24) ≠ 0 ∧
    memW s (globN s "bo" + 32) ≠ 0 ∧ locN s "index" < memW s (globN s "bo" + 80)

def BlockReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ 16 * memW s (memW s (locN s "si") + 40) + 16 < 2 ^ 64

def ReqsFresh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) = 0

def MsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧
    memW s (locN s "msg" + 152) ∈ S ∧ memW s (locN s "msg" + 160) ∈ S ∧
    Inside (locN s "msg", 176) sourceBase (globN s "heap_ptr") ∧ WordsOK s (locN s "msg", 176) ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "msg", 176) i) ∧
    (∀ j ∈ fixedObjects s, Disj (locN s "msg", 176) j) ∧
    AvoidsTries s S [(locN s "msg", 176)] ∧
    memW s (locN s "msg" + 40) < 2 ^ 63 ∧
    RolesOK s S (worldRoleSlots s ++
      [(memW s (locN s "msg" + 152), "frame.addr"), (memW s (locN s "msg" + 160), "frame.key")])
      (journalRoleSlots s)

def FrameOpenReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MsgReady s ∧ locN s "kind" = 0

def EvmInvAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s) ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

def MsgOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 176) ∧ WordsOK s (m, 176) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 176) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 176) j) ∧
  (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (m, 176) o) ∧
  AvoidsTries s S [(m, 176)]

def EvmMsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ MsgOwned s S (memW s (globN s "ev" + 112))

def NodeKind {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (x : String) (k : Nat) :
    Prop :=
  locN s x ∈ Nd ∧ memW s (locN s x) = k

def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

def NodeFnExit (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd, memW post n = memW s n) ∧
        (∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"]).map ofString → s.globals.lookup k = post.globals.lookup k) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

def NodeFn (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names req) (NodeFnExit names req) fname

def RetLe (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

def RetNibbles (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) →
    ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
      NibblesOK post p.toNat l.toNat ∧
      Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr")) fname

def ReqRoom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) < 8

def WorldTypedWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTypedWith s S Nd

def typedRecords : List (String × Nat) := [("ws", 40), ("bs", 80), ("ts", 72), ("bo", 88)]

def worldTypedIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  (S.flatMap (htabFootprint s) ++
    typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) ++
    [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s ++
    nodeExtents s Nd).map (fun i => if i.2 = 0 then (0, 0) else i)

def worldOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++ fixedObjects s ++ nodeExtents s Nd

def IvlsDisj (os js : List Ivl) : Prop := ∀ o ∈ os, ∀ j ∈ js, Disj o j

def freeGap {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")

def heapFree {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

def GlobalsKept (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ k : MlS, k ∉ (gw).map ofString → s.globals.lookup k = post.globals.lookup k

def RecordsKept (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (keep : List (String × List Nat)) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ r ∈ keep, globN s r.1 ≠ 0 → ∀ k ∈ r.2, (∀ i ∈ R s, ¬ CellHits (globN s r.1 + k) i) →
    memW post (globN s r.1 + k) = memW s (globN s r.1 + k)

def OwnedGrows {F : Type} (s post : PanSemStateFiniteExact 64 F) (old new : List Ivl) : Prop :=
  ∀ o ∈ new, o = (0, 0) ∨ (∃ j ∈ old, Inside o j.1 (j.1 + j.2)) ∨
    Inside o (globN s "heap_ptr") (globN post "heap_ptr")

def NoExtra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun _ _ _ _ _ => True

def WorldStep (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

def WorldKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStep R gw keep Q s r post) fname

def WorldStepIn (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → (∀ t ∈ T s, t ∈ S) → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

def WorldKeepsIn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStepIn T R gw keep Q s r post) fname

def EvmAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ ∃ Nd, TriesTypedWith s S Nd ∧
    IvlsDisj (R s) (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten)

def EvmStep (gw : List String) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post => EvmInv post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧ GlobalsKept gw s post ∧
    evmChain post = evmChain s

def EvmKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → EvmStep gw s post) fname

def mptObjIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (Nm : List Nat) (m : Nat) : List Ivl :=
  (m, 16) :: nodeExtents s Nm

def MptObjStep (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat)) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd Nm, WorldTypedWith s S Nd → MptObjInWith s S Nm (locN s "m") →
      IvlsDisj ((locN s "m", 16) :: R s ++ nodeExtents s Nm) (nodeExtents s Nd) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")) →
      ∃ S' Nd' Nm', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        MptObjInWith post S' Nm' (locN s "m") ∧
        IvlsDisj ((locN s "m", 16) :: nodeExtents post Nm') (nodeExtents post Nd') ∧
        OwnedGrows s post (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
          (worldOwned post S' Nd' ++ mptObjIvls post Nm' (locN s "m")) ∧
        FrameOutside s post
          (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++ R s ++ [freeGap s]) (heapFree s)

def MptKeeps (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat)) (fname : MlS) : Prop :=
  FunSpec MptObjReady (fun s r post => Resumes r → MptObjStep R gw keep s post) fname

def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def RetWord (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ Q s post w.toNat

def Returns (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop)
    (fname : MlS) : Prop :=
  FunSpec P (RetWord (fun s post p => ArenaReady post ∧ AllocatorGrows s post ∧ Q s post p)) fname

def RetMptObj : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    AllocatorGrows s post ∧
    ∃ Nm, MptObjInWith post S' Nm w.toNat ∧ IvlsDisj (mptObjIvls post Nm w.toNat) (nodeExtents post Nd') ∧
      ∀ o ∈ mptObjIvls post Nm w.toNat, o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr")

def RetAvoids (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    IvlsDisj (B s post w.toNat) (worldOwned post S' Nd')

def RetAvoidsIf (C : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
      List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => C s → RetAvoids B s r post S' Nd'

def RetListSlot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    w.toNat % 8 = 0 ∧ Inside (w.toNat, 8) (memW post (locN s "l"))
      (memW post (locN s "l") + 8 * memW post (locN s "l" + 16))

def BalChangeArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ ((locN s "which" = 16 ∧ locN s "esz" = 40) ∨
    (locN s "which" = 24 ∧ locN s "esz" = 16) ∨ (locN s "which" = 32 ∧ locN s "esz" = 24))

def FreshScratch {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ globN s "frame_mem_ptr" ≤ p ∧
    Inside (p, (n + 7) / 8 * 8) (globN post "scratch_ptr") (globN s "scratch_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def PushesFrame (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧
    (a.toNat = 0 → b.toNat = 0 ∨ FreshBlock s post b.toNat 32) ∧ (a.toNat ≠ 0 →
      FreshScratch s post b.toNat 88 ∧ (memW post (b.toNat + 8) = 1 ∨
        (memW post (b.toNat + 8) = 2 ∧ memW post (b.toNat + 32) = 0 ∧
          memW post (b.toNat + 40) = 0 ∧
          FreshBlock s post (memW post (b.toNat + 16)) 176)))) fname

def ResolvesNode (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∃ a b c d : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] ∧
    (a.toNat = 0 → b.toNat = 0 ∨ FreshBlock s post b.toNat 32)) fname

def InvalidatesCache (fname : MlS) : Prop :=
  FunSpec (NodeArgs ["nd"] (fun _ _ => True)) (fun s r post => Resumes r →
    post = { s with
      memory := fun a => if a = BitVec.ofNat 64 (locN s "nd" + 8) ∨ a = BitVec.ofNat 64 (locN s "nd" + 16) ∨
          a = BitVec.ofNat 64 (locN s "nd" + 24) then HolWordLab.word 0 else s.memory a,
      locals := post.locals, clock := post.clock }) fname

def ReqCountInc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s _ post _ _ => memW post (globN s "bo" + 64) = memW s (globN s "bo" + 64) + 1

def inputCells {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : List Ivl :=
  [(si, 8), (memW s si + 40, 8)]

def RetInput : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    (∀ i ∈ inputCells post w.toNat, i.1 % 8 = 0 ∧
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i) ∧
    IvlsDisj (inputCells post w.toNat) (worldOwned post S' Nd') ∧
    memW post (memW post w.toNat + 40) < 2 ^ 63

def InputAt {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ArenaReady s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ i ∈ inputCells s si, Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i) ∧
    IvlsDisj (inputCells s si) (worldOwned s S Nd) ∧
    memW s (memW s si + 40) < 2 ^ 63

def InputReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAt s (locN s "si")

def ArgNonNull (x : String) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → locN s x ≠ 0) fname

def ResumesInDomain (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Ivl) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → 0 < (R s).2 → Inside (R s) sourceBase heapEnd) fname

def BoListArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧
    (locN s "l" = memW s (globN s "bo" + 40) ∨ locN s "l" = memW s (globN s "bo" + 72)) ∧
    locN s "esz" = 8

def ZeroFills (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∀ a, locN s "dst" ≤ a →
    a + 8 ≤ locN s "dst" + locN s "n" → a % 8 = 0 → memW post a = 0) fname

def RetIntrinsic (fname : MlS) : Prop :=
  FunSpec GuestInv (fun _ r _ => ∀ v, r = some (.returned v) →
    ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] ∧
      a.toNat ≤ 16777216) fname

structure Hoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

def PostLocalsOnly (names : List String)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)),
    (∀ n ∈ names, locals.lookup (ofString n) = t.locals.lookup (ofString n)) →
    Q r t → Q r { t with locals := locals }
end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10

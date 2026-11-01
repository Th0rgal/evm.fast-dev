import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Support

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Assemble the head invariant and distinguish strict descent from an empty extension.
The hypotheses record the caller's actual assignments and exact memory effect. -/
theorem descent_post {F : Type} {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : MptInsertActive s) (hk : mptKind s = 2)
    (hat : ArenaReady t) (hn : NodeHeap t Nd) (hcurrent : locN s "node" ∈ Nd)
    (hkey : KeyIn t Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hparams : locN t "key" = locN s "key" ∧ locN t "klen" = locN s "klen" ∧
      locN t "vptr" = locN s "vptr" ∧ locN t "vlen" = locN s "vlen")
    (hlevel : locN t "level" = locN s "level" + memW s (locN s "node" + 40))
    (hsl : memW s (locN s "node" + 40) ≤ locN s "klen" - locN s "level")
    (hnode : locN t "node" = memW s (locN s "node" + 48))
    (hslot : locN t "slot" = locN s "node" + 48)
    (hresult : locN t "result" = if locN s "slot" = 0 then locN s "node" else locN s "result")
    (hmem : t = { clearCache s (locN s "node") with locals := t.locals, clock := t.clock })
    (hlocals : ∀ x : MlS, x ∉ (["go", "node", "slot", "level", "result"].map ofString) →
      t.locals.lookup x = s.locals.lookup x) :
    MptInsertHead t ∧ MptInsertEffect s t := by
  have hnonzero : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have htag : memW s (locN s "node") = 2 := by
    simpa only [mptKind, if_neg hnonzero] using hk
  obtain ⟨hlev, Nd0, hn0, hroot0, _, _, hvlen, hklen⟩ := ha.1.2 ha.2
  have hmember0 : locN s "node" ∈ Nd0 := hroot0.resolve_left hnonzero
  have hbound := (hn0.1 (locN s "node") hmember0).2.2.1.2
  change locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hbound
  rw [htag] at hbound
  change locN s "node" + 56 ≤ heapLimit at hbound
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hmemory := congrArg (fun z : PanSemStateFiniteExact 64 F => z.memory) hmem
  change t.memory = (clearCache s (locN s "node")).memory at hmemory
  have hsame (a : Nat) (ha64 : a < 2 ^ 64)
      (ha8 : a ≠ locN s "node" + 8) (ha16 : a ≠ locN s "node" + 16)
      (ha24 : a ≠ locN s "node" + 24) : memW t a = memW s a := by
    have hm := clearCache_memory_eq s (locN s "node") a ha64 (by omega) ha8 ha16 ha24
    simp only [memW, hmemory, hm]
  have htagt : memW t (locN s "node") = 2 :=
    (hsame _ (by omega) (by omega) (by omega) (by omega)).trans htag
  have hchild : memW t (locN s "node" + 48) = memW s (locN s "node" + 48) :=
    hsame _ (by omega) (by omega) (by omega) (by omega)
  refine ⟨⟨hat, fun _ => ?_⟩, ?_⟩
  · refine ⟨by rw [hlevel, hparams.2.1]; omega, Nd, hn, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnode, ← hchild]
      exact (hn.1 (locN s "node") hcurrent).2.2.2.2.1 htagt
    · have hsuf := keyIn_subrange hkey (off := memW s (locN s "node" + 40))
        (size := locN s "klen" - locN s "level" - memW s (locN s "node" + 40)) (by omega)
      simpa only [hparams.1, hparams.2.1, hlevel, Nat.add_assoc, Nat.sub_sub] using hsuf
    · exact Or.inr ⟨locN s "node", hcurrent, Or.inl ⟨htagt, hslot⟩,
        by rw [hslot, hchild, hnode]⟩
    · simpa only [hparams.2.2.2] using hvlen
    · simpa only [hparams.2.1] using hklen
  · refine Or.inr ⟨hparams.1, hparams.2.1, hparams.2.2.1, hparams.2.2.2, ?_⟩
    by_cases hz : memW s (locN s "node" + 40) = 0
    · exact Or.inr ⟨hnonzero, htag, hz, by simpa only [hz, Nat.add_zero] using hlevel,
        hnode, hslot, hresult, hmem, hlocals⟩
    · exact Or.inl (by omega)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2

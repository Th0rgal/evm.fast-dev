import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Eval

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestGlobalKeep

def mptInsertFinish : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
      (.assign .local (ofString "result") (.var .local (ofString "r")))
      (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))))
    (.seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
      (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
        (.assign .local (ofString "level") (.var .local (ofString "next_level")))))

def mptInsertDescent : ProgHOL 64 :=
  .seq (.assign .local (ofString "r") (.var .local (ofString "node")))
    (.seq (.assign .local (ofString "next_node")
      (.load .one (.op .add [.var .local (ofString "node"), .const 32,
        .panop .mul [.var .local (ofString "idx"), .const 8]])))
      (.seq (.assign .local (ofString "next_slot")
        (.op .add [.var .local (ofString "node"), .const 32,
          .panop .mul [.var .local (ofString "idx"), .const 8]]))
        (.seq (.assign .local (ofString "next_level")
          (.op .add [.var .local (ofString "level"), .const 1]))
          (.assign .local (ofString "go") (.const 1)))))

def mptInsertPayload : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "node"), .const 160]) (.var .local (ofString "vptr")))
    (.seq (.store (.op .add [.var .local (ofString "node"), .const 168]) (.var .local (ofString "vlen")))
      (.assign .local (ofString "r") (.var .local (ofString "node"))))

def mptInsertBranch : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))
    mptInsertPayload
    (.dec (ofString "idx") .one
      (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]))
      mptInsertDescent)

/-- The branch-node case uses only caller-local assignments and ordinary stores. -/
theorem mpt_arena_local_program {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (h : ArenaReady s)
    (hs : ∀ g : MlS, keepsG g (fun _ => false) p = true) :
    ArenaReady (evaluateHOLFiniteState s p).2 := by
  refine ⟨guestInv_evaluate s p h.1, ?_⟩
  have hg : (evaluateHOLFiniteState s p).2.globals = s.globals := by
    apply HolFiniteMapExact.ext
    funext g
    exact evaluate_keepsG g (fun _ => false) (fun _ hf => by contradiction)
      p (hs g) s h.1.code
  simpa only [ArenaOK, globN, hg] using h.2

theorem mpt_stopped_local_program {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (h : ArenaReady s) (hz : locN s "go" = 0)
    (hg : ∀ g : MlS, keepsG g (fun _ => false) p = true)
    (hl : avoidsLocal (ofString "go") p = true)
    (hf : Flowing (evaluateHOLFiniteState s p).1) :
    MptInsertHead (evaluateHOLFiniteState s p).2 ∧
      locN (evaluateHOLFiniteState s p).2 "go" = 0 := by
  have ha := mpt_arena_local_program s p h hg
  have he := evaluate_avoidsLocal_flowing (ofString "go") p hl s hf
  have hz' : locN (evaluateHOLFiniteState s p).2 "go" = 0 := by
    simpa only [locN, he] using hz
  exact ⟨⟨ha, fun hne => (hne hz').elim⟩, hz'⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

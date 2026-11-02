import InitECandidate.Solver.Wave8GuestInv.MemoryViews

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

theorem lookupCodeHOLFinite_installed_return {F : Type}
    (state : PanSemStateFiniteExact 64 F) (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body body' : ProgHOL 64) (ret ret' : ShapeHOL)
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : state.code.lookup fname = some (params, body, ret))
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ret' = ret := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    state.code.lookup fname values body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hc] at hx
  split at hx
  · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
  · cases hx

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
    ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k

def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

end InitECandidate.Solver.Wave8GuestInv

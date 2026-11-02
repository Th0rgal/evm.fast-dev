import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.DelRoot
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.DelInner

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8M19.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8M19

theorem del_core {F : Type} (s post : PanSemStateFiniteExact 64 F) (tw nd ow lw cw : BitVec 64)
    (M' : BitVec 64 → HolWordLab 64) (L I Fr : List Nat) (mvN : Nat)
    (hA : ArenaReady s) (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hB : HtabBlocks s tw.toNat)
    (hT : TreeWF L I Fr (hdr s tw.toNat 8) (hdr s tw.toNat 0) (hdr s tw.toNat 3) (hdr s tw.toNat 7)
      (hdr s tw.toNat 9) (nodeF s (hdr s tw.toNat 5)) (fun i => memW s (hdr s tw.toNat 6 + 8 * i)))
    (h5 : hdr s tw.toNat 5 = nd.toNat) (h6 : hdr s tw.toNat 6 = ow.toNat)
    (hcw : cw.toNat + 1 = hdr s tw.toNat 3)
    (hleaf : lw.toNat ∈ L)
    (hmvN : ∀ h : L.length - 1 < L.length, L[L.length - 1]'h = mvN) (hmvL : mvN ∈ L)
    (hMn : ∀ n off, n < hdr s tw.toNat 10 + 1 → off < 32 →
      rdN M' (nd.toNat + 32 * n + off) =
        if n = mvN ∧ off = 16 then nodeF s nd.toNat lw.toNat 16
        else rdN s.memory (nd.toNat + 32 * n + off))
    (hMo : ∀ i, i < hdr s tw.toNat 10 + 1 →
      rdN M' (ow.toNat + 8 * i) =
        if i = nodeF s nd.toNat lw.toNat 16 then mvN else rdN s.memory (ow.toNat + 8 * i))
    (hMh : ∀ c, c < 88 → rdN M' (tw.toNat + c) = rdN s.memory (tw.toNat + c))
    (hMf : ∀ a : BitVec 64, (∀ i ∈ htabFootprint s tw.toNat, ¬ InIvl a.toNat i) → M' a = s.memory a)
    (hpost : DelPostR s M' tw nd lw cw post) :
    ExitR9 tw.toNat s post := by
  by_cases h : wv (updW M' (tw + 24) cw (tw + 56)) = lw
  · exact del_core_root s post tw nd ow lw cw M' L I Fr mvN hA hal hB hT h5 h6 hcw hleaf hmvN hmvL hMn hMo hMh hMf hpost h
  · exact del_core_inner s post tw nd ow lw cw M' L I Fr mvN hA hal hB hT h5 h6 hcw hleaf hmvN hmvL hMn hMo hMh hMf hpost h

end InitECandidate.Solver.Wave8M19.Htab

import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.SupportBase
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.Helpers

set_option Elab.async false

/-! Source: ExtraNames.lean; Opus port from 3ea193df0. -/

/-! Additional AST-local names, extracted from Opus Names.lean at 3ea193df0. -/
namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack.Basis.Pure.MlString
@[simp] theorem nm_t_order : (ofString "t" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_moved : (ofString "t" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_order : (ofString "stride" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_moved : (ofString "stride" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_order : (ofString "keys" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_moved : (ofString "keys" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_order : (ofString "nodes" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_moved : (ofString "nodes" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_t : (ofString "order" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_stride : (ofString "order" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_keys : (ofString "order" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_nodes : (ofString "order" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_n : (ofString "order" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_p : (ofString "order" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_b : (ofString "order" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_keybits : (ofString "order" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_key : (ofString "order" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_leaf : (ofString "order" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_klen : (ofString "order" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_eq : (ofString "order" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_pos : (ofString "order" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_count : (ofString "order" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_moved : (ofString "order" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_g : (ofString "order" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_order_s : (ofString "order" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_order : (ofString "n" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_moved : (ofString "n" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_order : (ofString "p" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_moved : (ofString "p" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_order : (ofString "b" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_moved : (ofString "b" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_order : (ofString "keybits" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_moved : (ofString "keybits" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_order : (ofString "key" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_moved : (ofString "key" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_order : (ofString "leaf" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_moved : (ofString "leaf" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_order : (ofString "klen" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_moved : (ofString "klen" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_order : (ofString "eq" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_moved : (ofString "eq" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_order : (ofString "pos" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_moved : (ofString "pos" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_order : (ofString "count" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_moved : (ofString "count" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_t : (ofString "moved" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_stride : (ofString "moved" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_keys : (ofString "moved" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_nodes : (ofString "moved" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_order : (ofString "moved" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_n : (ofString "moved" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_p : (ofString "moved" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_b : (ofString "moved" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_keybits : (ofString "moved" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_key : (ofString "moved" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_leaf : (ofString "moved" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_klen : (ofString "moved" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_eq : (ofString "moved" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_pos : (ofString "moved" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_count : (ofString "moved" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_g : (ofString "moved" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_moved_s : (ofString "moved" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_order : (ofString "g" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_moved : (ofString "g" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_order : (ofString "s" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_moved : (ofString "s" = ofString "moved") = False := by simp only [eq_iff_iff, iff_false]; decide

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelProgress.lean; Opus port from 3ea193df0. -/

/-! `htab_del_progress_spec`. A normal return of `htab_del` either went through one of the two
`return 0` exits — only `htab_find_leaf` and `memeq` ran, both local-only, so the post-state is
the entry state up to locals and clock — or deleted: it stored `count - 1` at `t+24`, and every
later store hits a node of the table (`HtabWF` bounds the indices it reads), never `t+24`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

theorem lookup_memeq' :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ((extractFn Guest.Software.guestFn_memeq).params.map
          InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_memeq).body,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural
          (extractFn Guest.Software.guestFn_memeq).returnShape) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem memeq_locOnlyW : locOnlyW (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_memeq).body) = true := by
  htab_unfold Guest.Software.guestFn_memeq
  rfl

theorem lookup_find_leaf' :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_htab_find_leaf).body, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

/-- `seq (ite c y n) rest` by the outcome of the test. -/
theorem Ret.seq_ite {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n rest : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ w, ev s c = some (.val (.word w)) →
      (w ≠ 0 → Ret s (.seq y rest) Φ) ∧ (w = 0 → Ret s (.seq n rest) Φ)) :
    Ret s (.seq (.ite c y n) rest) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hv ⊢
  revert hv
  split
  · rename_i w hw
    split
    · rename_i hz
      intro hv
      have := (h w hw).2 hz v
      rw [evaluateHOLFiniteState_seq_line780] at this
      exact this hv
    · rename_i hz
      intro hv
      have := (h w hw).1 hz v
      rw [evaluateHOLFiniteState_seq_line780] at this
      exact this hv
  · simp

theorem Ret.seq_return {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {rest : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.seq (.return e) rest) Φ := by
  refine Ret.seq (Ret.ret h) ?_
  intro t ht
  rw [evaluateHOLFiniteState_return] at ht
  revert ht
  split
  · simp
  · split <;> simp

theorem Ret.seq_skip {F : Type} {s : PanSemStateFiniteExact 64 F} {rest : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (h : Ret s rest Φ) :
    Ret s (.seq .skip rest) Φ := by
  refine Ret.seq Ret.skip_noret ?_
  intro t ht
  rw [evaluateHOLFiniteState_skip] at ht
  cases ht
  exact h

/-- The deletion tail of `htab_del`, from `st t+24, count` to `return 1`. -/
def delRest : ProgHOL 64 :=
  ((ProgHOL.store
                                  (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 24#64])
                                  (ExpHOL.var VarKind.local (ofString "count"))).seq
                              ((ProgHOL.ite
                                    (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "leaf"))
                                      (ExpHOL.load ShapeHOL.one
                                        (ExpHOL.op BinOp.add
                                          [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 56#64])))
                                    (ProgHOL.store
                                      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 56#64])
                                      (ExpHOL.const 0#64))
                                    (ProgHOL.dec (ofString "p") ShapeHOL.one
                                      (ExpHOL.load ShapeHOL.one
                                        (ExpHOL.op BinOp.add
                                          [ExpHOL.var VarKind.local (ofString "nodes"),
                                            ExpHOL.panop PanOp.mul
                                              [ExpHOL.var VarKind.local (ofString "leaf"), ExpHOL.const 32#64],
                                            ExpHOL.const 0#64]))
                                      (ProgHOL.dec (ofString "g") ShapeHOL.one
                                        (ExpHOL.load ShapeHOL.one
                                          (ExpHOL.op BinOp.add
                                            [ExpHOL.var VarKind.local (ofString "nodes"),
                                              ExpHOL.panop PanOp.mul
                                                [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64],
                                              ExpHOL.const 0#64]))
                                        (ProgHOL.dec (ofString "s") ShapeHOL.one
                                          (ExpHOL.load ShapeHOL.one
                                            (ExpHOL.op BinOp.add
                                              [ExpHOL.var VarKind.local (ofString "nodes"),
                                                ExpHOL.panop PanOp.mul
                                                  [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64],
                                                ExpHOL.const 8#64]))
                                          ((ProgHOL.ite
                                                (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "s"))
                                                  (ExpHOL.var VarKind.local (ofString "leaf")))
                                                (ProgHOL.assign VarKind.local (ofString "s")
                                                  (ExpHOL.load ShapeHOL.one
                                                    (ExpHOL.op BinOp.add
                                                      [ExpHOL.var VarKind.local (ofString "nodes"),
                                                        ExpHOL.panop PanOp.mul
                                                          [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64],
                                                        ExpHOL.const 16#64])))
                                                ProgHOL.skip).seq
                                            ((ProgHOL.store
                                                  (ExpHOL.op BinOp.add
                                                    [ExpHOL.var VarKind.local (ofString "nodes"),
                                                      ExpHOL.panop PanOp.mul
                                                        [ExpHOL.var VarKind.local (ofString "s"), ExpHOL.const 32#64],
                                                      ExpHOL.const 0#64])
                                                  (ExpHOL.var VarKind.local (ofString "g"))).seq
                                              ((ProgHOL.ite
                                                    (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "g"))
                                                      (ExpHOL.const 0#64))
                                                    (ProgHOL.store
                                                      (ExpHOL.op BinOp.add
                                                        [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 56#64])
                                                      (ExpHOL.var VarKind.local (ofString "s")))
                                                    (ProgHOL.ite
                                                      (ExpHOL.cmp Cmp.equal
                                                        (ExpHOL.load ShapeHOL.one
                                                          (ExpHOL.op BinOp.add
                                                            [ExpHOL.var VarKind.local (ofString "nodes"),
                                                              ExpHOL.panop PanOp.mul
                                                                [ExpHOL.var VarKind.local (ofString "g"),
                                                                  ExpHOL.const 32#64],
                                                              ExpHOL.const 8#64]))
                                                        (ExpHOL.var VarKind.local (ofString "p")))
                                                      (ProgHOL.store
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "nodes"),
                                                            ExpHOL.panop PanOp.mul
                                                              [ExpHOL.var VarKind.local (ofString "g"),
                                                                ExpHOL.const 32#64],
                                                            ExpHOL.const 8#64])
                                                        (ExpHOL.var VarKind.local (ofString "s")))
                                                      (ProgHOL.store
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "nodes"),
                                                            ExpHOL.panop PanOp.mul
                                                              [ExpHOL.var VarKind.local (ofString "g"),
                                                                ExpHOL.const 32#64],
                                                            ExpHOL.const 16#64])
                                                        (ExpHOL.var VarKind.local (ofString "s"))))).seq
                                                ((ProgHOL.store
                                                      (ExpHOL.op BinOp.add
                                                        [ExpHOL.var VarKind.local (ofString "nodes"),
                                                          ExpHOL.panop PanOp.mul
                                                            [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64],
                                                          ExpHOL.const 0#64])
                                                      (ExpHOL.load ShapeHOL.one
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "t"),
                                                            ExpHOL.const 72#64]))).seq
                                                  (ProgHOL.store
                                                    (ExpHOL.op BinOp.add
                                                      [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 72#64])
                                                    (ExpHOL.var VarKind.local (ofString "p"))))))))))).seq
                                ((ProgHOL.store
                                      (ExpHOL.op BinOp.add
                                        [ExpHOL.var VarKind.local (ofString "nodes"),
                                          ExpHOL.panop PanOp.mul
                                            [ExpHOL.var VarKind.local (ofString "leaf"), ExpHOL.const 32#64],
                                          ExpHOL.const 0#64])
                                      (ExpHOL.load ShapeHOL.one
                                        (ExpHOL.op BinOp.add
                                          [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 72#64]))).seq
                                  ((ProgHOL.store
                                        (ExpHOL.op BinOp.add
                                          [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 72#64])
                                        (ExpHOL.var VarKind.local (ofString "leaf"))).seq
                                    (ProgHOL.return (ExpHOL.const 1#64))))))

/-- `a ≠ b` for word addresses by their numeric values. -/
macro "addr_neq" : tactic => `(tactic| (
  intro hh0
  have hh := congrArg BitVec.toNat hh0
  simp [BitVec.toNat_add, BitVec.toNat_mul] at hh
  omega))

theorem ofNat_add_toNat' (t : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (t.toNat + n) = t + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem Ret.mono {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (h : Ret s p Φ)
    (hΦ : ∀ v t, Φ v t → Ψ v t) : Ret s p Ψ := fun v hv => hΦ _ _ (h v hv)

/-- The splice in the non-root branch of the deletion tail: from `st nodes+s*32, g` on. -/
def delRest3 : ProgHOL 64 :=
  ((ProgHOL.store
                                                  (ExpHOL.op BinOp.add
                                                    [ExpHOL.var VarKind.local (ofString "nodes"),
                                                      ExpHOL.panop PanOp.mul
                                                        [ExpHOL.var VarKind.local (ofString "s"), ExpHOL.const 32#64],
                                                      ExpHOL.const 0#64])
                                                  (ExpHOL.var VarKind.local (ofString "g"))).seq
                                              ((ProgHOL.ite
                                                    (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "g"))
                                                      (ExpHOL.const 0#64))
                                                    (ProgHOL.store
                                                      (ExpHOL.op BinOp.add
                                                        [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 56#64])
                                                      (ExpHOL.var VarKind.local (ofString "s")))
                                                    (ProgHOL.ite
                                                      (ExpHOL.cmp Cmp.equal
                                                        (ExpHOL.load ShapeHOL.one
                                                          (ExpHOL.op BinOp.add
                                                            [ExpHOL.var VarKind.local (ofString "nodes"),
                                                              ExpHOL.panop PanOp.mul
                                                                [ExpHOL.var VarKind.local (ofString "g"),
                                                                  ExpHOL.const 32#64],
                                                              ExpHOL.const 8#64]))
                                                        (ExpHOL.var VarKind.local (ofString "p")))
                                                      (ProgHOL.store
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "nodes"),
                                                            ExpHOL.panop PanOp.mul
                                                              [ExpHOL.var VarKind.local (ofString "g"),
                                                                ExpHOL.const 32#64],
                                                            ExpHOL.const 8#64])
                                                        (ExpHOL.var VarKind.local (ofString "s")))
                                                      (ProgHOL.store
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "nodes"),
                                                            ExpHOL.panop PanOp.mul
                                                              [ExpHOL.var VarKind.local (ofString "g"),
                                                                ExpHOL.const 32#64],
                                                            ExpHOL.const 16#64])
                                                        (ExpHOL.var VarKind.local (ofString "s"))))).seq
                                                ((ProgHOL.store
                                                      (ExpHOL.op BinOp.add
                                                        [ExpHOL.var VarKind.local (ofString "nodes"),
                                                          ExpHOL.panop PanOp.mul
                                                            [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64],
                                                          ExpHOL.const 0#64])
                                                      (ExpHOL.load ShapeHOL.one
                                                        (ExpHOL.op BinOp.add
                                                          [ExpHOL.var VarKind.local (ofString "t"),
                                                            ExpHOL.const 72#64]))).seq
                                                  (ProgHOL.store
                                                    (ExpHOL.op BinOp.add
                                                      [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 72#64])
                                                    (ExpHOL.var VarKind.local (ofString "p"))))))

/-- The post-state shape that the deletion tail needs. -/
def DelQ {F : Type} (s : PanSemStateFiniteExact 64 F) (C : Nat) (tw nd lw cw : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64),
    t = NS s L s.globals M C ∧ L.lookup (ofString "t") = some (.val (.word tw)) ∧
    L.lookup (ofString "nodes") = some (.val (.word nd)) ∧
    L.lookup (ofString "leaf") = some (.val (.word lw)) ∧ M (tw + 24) = .word cw

theorem DelQ.locals {F : Type} {s : PanSemStateFiniteExact 64 F} {C : Nat} {tw nd lw cw : BitVec 64}
    {t : PanSemStateFiniteExact 64 F} (h : DelQ s C tw nd lw cw t) (x : MlS) (o : Option (ValueHOL 64))
    (hx1 : ofString "t" ≠ x) (hx2 : ofString "nodes" ≠ x) (hx3 : ofString "leaf" ≠ x) :
    DelQ s C tw nd lw cw { t with locals := HolFiniteMapExact.resVarEq t.locals (x, o) } := by
  obtain ⟨L, M, rfl, h1, h2, h3, h4⟩ := h
  refine ⟨HolFiniteMapExact.resVarEq L (x, o), M, rfl, ?_, ?_, ?_, h4⟩ <;>
    rw [PanRunBounded.resVarEq_lookup] <;> simp [*, Ne.symm hx1, Ne.symm hx2, Ne.symm hx3]

theorem Ret.run {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (h : Ret s p Φ) (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s p).1 = some (.returned v)) :
    Φ v (evaluateHOLFiniteState s p).2 := h v hv

theorem Ret.ns_storeV {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hev : ∀ v, ev (NS s L G M C) e = some v → ∃ w, v = .val (.word w))
    (hb : ∀ (a w : BitVec 64), ev (NS s L G M C) d = some (.val (.word a)) →
      ev (NS s L G M C) e = some (.val (.word w)) → s.memaddrs a →
      Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a val m hd he hm
  obtain ⟨w, rfl⟩ := hev val he
  obtain ⟨hdom, rfl⟩ := stores_word _ hm
  exact hb a w hd he hdom

theorem NoRet.store' {d e : ExpHOL 64} : NoRet (.store d e) := by
  intro F st v
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem ev_load_word {F : Type} (X : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (h : ev X (.load .one e) = some v) : ∃ w, v = .val (.word w) := by
  simp only [ev, evalHOLExact] at h
  revert h
  split
  · intro h
    simp only [memLoadHOLExact] at h
    split at h
    · rename_i a _
      split at h
      · injection h with h
        subst h
        rcases X.memory a with ⟨w⟩
        exact ⟨w, rfl⟩
      · cases h
    · cases h
  · intro h; cases h

theorem ev_var_word {F : Type} (X : PanSemStateFiniteExact 64 F) (x : MlS) (w : BitVec 64)
    (h1 : X.locals.lookup x = some (.val (.word w))) (v : ValueHOL 64)
    (h : ev X (.var .local x) = some v) : ∃ w, v = .val (.word w) := by
  rw [ev_var X x _ h1] at h
  simp only [Option.some.injEq] at h
  exact ⟨w, h.symm⟩

theorem Ret.seq_flw {F : Type} {X : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hna : NoRet a)
    (hF : Flw X a (fun r t => r = none → Ret t b Φ)) : Ret X (.seq a b) Φ := by
  refine Ret.seq (fun v hv => absurd hv (hna X v)) ?_
  intro t ht
  have := hF (by rw [ht]; left; rfl)
  rw [ht] at this
  exact this rfl

theorem ev_idx_addr_eq {F : Type} (X : PanSemStateFiniteExact 64 F) (bx ix : MlS)
    (b i sc off a : BitVec 64)
    (h : ev X (.op .add [.var .local bx, .panop .mul [.var .local ix, .const sc], .const off]) =
      some (.val (.word a)))
    (h1 : X.locals.lookup bx = some (.val (.word b)))
    (h2 : X.locals.lookup ix = some (.val (.word i))) : a = b + i * sc + off := by
  rw [ev_idx_addr X bx ix b i sc off h1 h2] at h
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at h
  exact h.symm

theorem Flw.mono {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Ψ1 Ψ2 : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (h : Flw s p Ψ1) (hΨ : ∀ r t, Ψ1 r t → Ψ2 r t) : Flw s p Ψ2 :=
  fun hf => hΨ _ _ (h hf)

theorem Flw.storeV {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hev : ∀ v, ev s e = some v → ∃ w, v = .val (.word w))
    (h : ∀ (a w : BitVec 64), ev s d = some (.val (.word a)) → ev s e = some (.val (.word w)) →
      s.memaddrs a → Ψ none { s with memory := updW s.memory a w }) :
    Flw s (.store d e) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_store] at hf ⊢
  revert hf
  split
  · rename_i a hd
    split
    · rename_i val he
      split
      · rename_i m hm
        intro _
        obtain ⟨w, rfl⟩ := hev val he
        obtain ⟨hdom, rfl⟩ := stores_word _ hm
        exact h a w hd he hdom
      · intro hf; rcases hf with h | h | h <;> cases h
    · intro hf; rcases hf with h | h | h <;> cases h
  · intro hf; rcases hf with h | h | h <;> cases h

attribute [local irreducible] Ret Flw in
theorem del_rest3 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw cw p0 g0 sv : BitVec 64) (Nn : Nat)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hLp : L.lookup (ofString "p") = some (.val (.word p0)))
    (hLg : L.lookup (ofString "g") = some (.val (.word g0)))
    (hLs : L.lookup (ofString "s") = some (.val (.word sv)))
    (hl1 : tw.toNat + 88 ≤ 2 ^ 64) (hl2 : nd.toNat + 32 * Nn ≤ 2 ^ 64)
    (hd1 : tw.toNat + 88 ≤ nd.toNat ∨ nd.toNat + 32 * Nn ≤ tw.toNat)
    (hpN : p0.toNat < Nn) (hgN : g0 = 0 ∨ g0.toNat < Nn) (hsN : sv.toNat < Nn)
    (h24 : M (tw + 24) = .word cw) :
    Flw (NS s L s.globals M C) delRest3 (fun r t => r = none → DelQ s C tw nd lw cw t) := by
  have htw := tw.isLt
  have hndl := nd.isLt
  have hp0l := p0.isLt
  have hg0l := g0.isLt
  have hsvl := sv.isLt
  unfold delRest3
  apply Flw.seq
  apply Flw.storeW (nd + sv * 32 + 0) g0 (ev_idx_addr _ _ _ nd sv 32 0 hLn hLs) (ev_var _ _ _ hLg)
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  have h24a : updW M (nd + sv * 32 + 0) g0 (tw + 24) = .word cw := by
    rw [updW_ne _ _ _ _ (by addr_neq)]; exact h24
  apply Flw.seq
  apply Flw.ite
  intro c hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
  simp [evalAt, evalHOLExact, hLg] at ha hb
  subst ha hb
  refine ⟨fun hc1 => ?_, fun hc0 => ?_⟩
  · apply Flw.storeW (tw + 56) sv (ev_fld_addr _ _ tw 56 hLt) (ev_var _ _ _ hLs)
    intro _
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.seq
    apply Flw.storeV (fun v h => ev_load_word _ _ v h)
    intro a1 w1 hd1' _ _
    obtain rfl := ev_idx_addr_eq _ _ _ nd p0 32 0 a1 hd1' (by simpa using hLn) (by simpa using hLp)
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.storeW (tw + 72) p0 (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLp)
    intro _ _
    refine ⟨L, _, rfl, hLt, hLn, hLl, ?_⟩
    show updW (updW (updW (updW M (nd + sv * 32 + 0) g0) (tw + 56) sv) (nd + p0 * 32 + 0) w1)
      (tw + 72) p0 (tw + 24) = .word cw
    rw [updW_ne _ _ _ _ (by addr_neq), updW_ne _ _ _ _ (by addr_neq),
      updW_ne _ _ _ _ (by addr_neq)]
    exact h24a
  · have hg0 : g0 ≠ 0 := by
      intro h; subst h hc0
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    have hgN' : g0.toNat < Nn := hgN.resolve_left hg0
    have hrest : ∀ off : BitVec 64, off.toNat < 32 →
        updW (updW M (nd + sv * 32 + 0) g0) (nd + g0 * 32 + off) sv (tw + 24) = .word cw := by
      intro off hoff
      rw [updW_ne _ _ _ _ (by addr_neq)]; exact h24a
    apply Flw.ite
    intro c2 _
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    all_goals
      first
      | apply Flw.storeW (nd + g0 * 32 + 8) sv (ev_idx_addr _ _ _ nd g0 32 8 hLn hLg) (ev_var _ _ _ hLs)
      | apply Flw.storeW (nd + g0 * 32 + 16) sv (ev_idx_addr _ _ _ nd g0 32 16 hLn hLg) (ev_var _ _ _ hLs)
      intro _
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.seq
      apply Flw.storeV (fun v h => ev_load_word _ _ v h)
      intro a1 w1 hd1' _ _
      obtain rfl := ev_idx_addr_eq _ _ _ nd p0 32 0 a1 hd1' (by simpa using hLn) (by simpa using hLp)
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.storeW (tw + 72) p0 (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLp)
      intro _ _
      refine ⟨L, _, rfl, hLt, hLn, hLl, ?_⟩
      simp only [NS_memory]
      rw [updW_ne _ _ _ _ (by addr_neq), updW_ne _ _ _ _ (by addr_neq), hrest _ (by decide)]

attribute [local irreducible] Ret in
theorem del_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw cw : BitVec 64) (Nn : Nat)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hl1 : tw.toNat + 88 ≤ 2 ^ 64) (hl2 : nd.toNat + 32 * Nn ≤ 2 ^ 64)
    (hd1 : tw.toNat + 88 ≤ nd.toNat ∨ nd.toNat + 32 * Nn ≤ tw.toNat)
    (hlwN : lw.toNat < Nn) (h24 : M (tw + 24) = .word cw) :
    Ret (NS s L s.globals M C)
      (.seq (.store (.op .add [.var .local (ofString "nodes"),
          .panop .mul [.var .local (ofString "leaf"), .const 32], .const 0])
          (.load .one (.op .add [.var .local (ofString "t"), .const 72])))
        (.seq (.store (.op .add [.var .local (ofString "t"), .const 72]) (.var .local (ofString "leaf")))
          (.return (.const 1))))
      (fun _ post => post.memory (tw + 24) = .word cw) := by
  have htw := tw.isLt
  have hndl := nd.isLt
  have hlwl := lw.isLt
  apply Ret.ns_storeV (fun v h => ev_load_word _ _ v h)
  intro a1 w1 hd1 _ _
  rw [ev_idx_addr _ _ _ nd lw 32 0 hLn hLl] at hd1
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd1
  subst hd1
  apply Ret.ns_storeW (tw + 72) lw (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLl)
  intro _
  apply Ret.ns_ret
  intro _ _
  show updW (updW M (nd + lw * 32 + 0) w1) (tw + 72) lw (tw + 24) = .word cw
  rw [updW_ne _ _ _ _ (by addr_neq), updW_ne _ _ _ _ (by addr_neq)]
  exact h24

attribute [local irreducible] Ret Flw in
theorem del_rest {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw cw rt : BitVec 64) (Nn : Nat)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hLc : L.lookup (ofString "count") = some (.val (.word cw)))
    (hl1 : tw.toNat + 88 ≤ 2 ^ 64) (hl2 : nd.toNat + 32 * Nn ≤ 2 ^ 64)
    (hd1 : tw.toNat + 88 ≤ nd.toNat ∨ nd.toNat + 32 * Nn ≤ tw.toNat)
    (hlwN : lw.toNat < Nn)
    (hM56 : M (tw + 56) = .word rt)
    (hpar : lw ≠ rt → ∀ p, M (nd + lw * 32 + 0) = .word p → p.toNat < Nn ∧
        (∀ g, M (nd + p * 32 + 0) = .word g → g = 0 ∨ g.toNat < Nn) ∧
        (∀ c, M (nd + p * 32 + 8) = .word c → c.toNat < Nn) ∧
        (∀ c, M (nd + p * 32 + 16) = .word c → c.toNat < Nn)) :
    Ret (NS s L s.globals M C) delRest (fun _ post => post.memory (tw + 24) = .word cw) := by
  have htw := tw.isLt
  have hndl := nd.isLt
  have hlwl := lw.isLt
  unfold delRest
  apply Ret.ns_storeW (tw + 24) cw (ev_fld_addr _ _ tw 24 hLt) (ev_var _ _ _ hLc)
  intro _
  set M1 := updW M (tw + 24) cw with hM1
  have hM1r : ∀ a, a ≠ tw + 24 → M1 a = M a := fun a h => updW_ne _ _ _ _ h
  have h24 : M1 (tw + 24) = .word cw := updW_eq _ _ _
  apply Ret.seq_ite
  intro c hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
  have ha' : a = lw := by
    simp [evalAt, evalHOLExact, hLl] at ha; exact ha.symm
  have hb' : b = rt := by
    obtain ⟨_, hbv⟩ := ev_field_load (NS s L s.globals M1 C) _ tw 56 hLt _ hb
    simp only [NS_memory] at hbv
    rw [hM1r _ (by addr_neq), hM56] at hbv
    simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hbv
    exact hbv
  subst ha' hb'
  refine ⟨fun hc1 => ?_, fun hc0 => ?_⟩
  · apply Ret.ns_storeW (tw + 56) 0 (ev_fld_addr _ _ tw 56 hLt) (by simp [ev, evalHOLExact])
    intro _
    exact del_tail s L _ C tw nd a cw Nn hLt hLn hLl hl1 hl2 hd1 hlwN
      (by rw [updW_ne _ _ _ _ (by addr_neq)]; exact h24)
  · have hne : a ≠ b := by
      intro h; subst h; subst hc0
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    apply Ret.seq_flw
    · exact NoRet.dec' (NoRet.dec' (NoRet.dec' (NoRet.seq (NoRet.ite NoRet.assign NoRet.skip)
        (NoRet.seq NoRet.store' (NoRet.seq (NoRet.ite NoRet.store' (NoRet.ite NoRet.store' NoRet.store'))
          (NoRet.seq NoRet.store' NoRet.store'))))))
    apply Flw.dec
    intro pv hpv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd a 32 0 (by simpa using hLn) (by simpa using hLl) pv hpv
    simp only [NS_memory]
    rw [hM1r _ (by addr_neq)]
    rcases hp0 : M (nd + a * 32 + 0) with ⟨p0⟩
    obtain ⟨hp0N, hgN, hs8N, hs16N⟩ := hpar hne p0 hp0
    have hp0l := p0.isLt
    show Flw (NS s (L.update (ofString "p", .val (.word p0))) s.globals M1 C) _ _
    apply Flw.dec
    intro gv hgv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 0
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hLn])
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE]) gv hgv
    simp only [NS_memory]
    rw [hM1r _ (by addr_neq)]
    rcases hg0 : M (nd + p0 * 32 + 0) with ⟨g0⟩
    have hg0N := hgN g0 hg0
    show Flw (NS s ((L.update (ofString "p", .val (.word p0))).update (ofString "g", .val (.word g0)))
      s.globals M1 C) _ _
    apply Flw.dec
    intro sv hsv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 8
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hLn])
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE]) sv hsv
    simp only [NS_memory]
    rw [hM1r _ (by addr_neq)]
    rcases hs0 : M (nd + p0 * 32 + 8) with ⟨s0⟩
    have hs0N := hs8N s0 hs0
    set L5 := ((L.update (ofString "p", .val (.word p0))).update (ofString "g", .val (.word g0))).update
      (ofString "s", .val (.word s0)) with hL5
    have hL5t : L5.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLt]
    have hL5n : L5.lookup (ofString "nodes") = some (.val (.word nd)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLn]
    have hL5l : L5.lookup (ofString "leaf") = some (.val (.word a)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLl]
    have hL5p : L5.lookup (ofString "p") = some (.val (.word p0)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE]
    have hL5g : L5.lookup (ofString "g") = some (.val (.word g0)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE]
    show Flw (NS s L5 s.globals M1 C) _ _
    apply Flw.seq
    apply Flw.ite
    intro c3 _
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 16 hL5n hL5p v hv
      simp only [NS_memory]
      rw [hM1r _ (by addr_neq)]
      rcases hs1 : M (nd + p0 * 32 + 16) with ⟨s1⟩
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      refine Flw.mono (del_rest3 s _ M1 C tw nd a cw p0 g0 s1 Nn
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5t])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5n])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5l])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5p])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5g])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hl1 hl2 hd1 hp0N hg0N (hs16N s1 hs1) h24) ?_
      intro r t hQ hr
      obtain ⟨L', M', rfl, h1, h2, h3, h4⟩ := hQ hr
      exact del_tail s _ M' C tw nd a cw Nn
        (by simp [PanRunBounded.resVarEq_lookup, h1]) (by simp [PanRunBounded.resVarEq_lookup, h2])
        (by simp [PanRunBounded.resVarEq_lookup, h3]) hl1 hl2 hd1 hlwN h4
    · apply Flw.skip
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      refine Flw.mono (del_rest3 s _ M1 C tw nd a cw p0 g0 s0 Nn hL5t hL5n hL5l hL5p hL5g
        (by simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE])
        hl1 hl2 hd1 hp0N hg0N hs0N h24) ?_
      intro r t hQ hr
      obtain ⟨L', M', rfl, h1, h2, h3, h4⟩ := hQ hr
      exact del_tail s _ M' C tw nd a cw Nn
        (by simp [PanRunBounded.resVarEq_lookup, h1]) (by simp [PanRunBounded.resVarEq_lookup, h2])
        (by simp [PanRunBounded.resVarEq_lookup, h3]) hl1 hl2 hd1 hlwN h4


attribute [local irreducible] Ret Flw in
theorem del_walk {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (tw : BitVec 64) (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, s.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, s.memory (tw + 40) = .word nd → s.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW s (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW s (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW s (nd.toNat + 32 * w.toNat + 16) ∈ S)
    (nd ow cntw rt : BitVec 64) (hnd : s.memory (tw + 40) = .word nd)
    (how : s.memory (tw + 48) = .word ow) (hcnt : s.memory (tw + 24) = .word cntw)
    (hrt : s.memory (tw + 56) = .word rt) (Nn : Nat)
    (hl1 : tw.toNat + 88 ≤ 2 ^ 64) (hl2 : nd.toNat + 32 * Nn ≤ 2 ^ 64)
    (hl3 : ow.toNat + 8 * Nn ≤ 2 ^ 64)
    (hd1 : tw.toNat + 88 ≤ nd.toNat ∨ nd.toNat + 32 * Nn ≤ tw.toNat)
    (hd2 : tw.toNat + 88 ≤ ow.toNat ∨ ow.toNat + 8 * Nn ≤ tw.toNat)
    (hd3 : nd.toNat + 32 * Nn ≤ ow.toNat ∨ ow.toNat + 8 * Nn ≤ nd.toNat)
    (hSN : ∀ x ∈ S, x < Nn) (Lset Iset : List Nat) (hLI : ∀ x ∈ Lset, x ∉ Iset)
    (hcnt1 : ∀ lw : BitVec 64, lw.toNat ∈ S → lw ≠ 0 → 1 ≤ cntw.toNat)
    (hpos : ∀ lw : BitVec 64, lw.toNat ∈ S → lw ≠ 0 →
      ∀ u, s.memory (nd + lw * 32 + 16) = .word u → u.toNat < Nn)
    (hmv : ∀ lw : BitVec 64, lw.toNat ∈ S → lw ≠ 0 →
      ∀ u, s.memory (ow + (cntw - 1) * 8) = .word u → u.toNat < Nn ∧ u.toNat ∈ Lset)
    (hpar : ∀ lw : BitVec 64, lw.toNat ∈ S → lw ≠ 0 → lw ≠ rt →
      ∀ p, s.memory (nd + lw * 32 + 0) = .word p → p.toNat ∈ Iset ∧ p.toNat < Nn ∧
        (∀ g, s.memory (nd + p * 32 + 0) = .word g → g = 0 ∨ g.toNat < Nn) ∧
        (∀ c, s.memory (nd + p * 32 + 8) = .word c → c.toNat < Nn) ∧
        (∀ c, s.memory (nd + p * 32 + 16) = .word c → c.toNat < Nn)) :
    Ret s (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_del).body)
      (fun _ post => HtabDelProgress s post) := by
  htab_unfold Guest.Software.guestFn_htab_del
  apply Ret.dec
  intro klv hklv
  apply Ret.dec
  intro stv hstv
  set s2 := setVarHOLFinite (ofString "stride") stv (setVarHOLFinite (ofString "klen") klv s)
    with hs2
  have ht2 : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]
  apply Ret.decCall_gen
  intro values body callee ret lv fpost hargs hl hrun
  have hlook := lookup_find_leaf'
  have hsame := lookupCodeHOLFinite_installed_body s2.code.lookup (ofString "htab_find_leaf") _ _
    body _ ret values callee (by rw [show s2.code = s.code from rfl, hcode]; exact hlook) hl
  subst hsame
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s2 _ _ hargs
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s2.code.lookup (ofString "htab_find_leaf") []
    (ofString "t") .one [(ofString "key", .one)] _ _ (by simp)
    (by rw [show s2.code = s.code from rfl, hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hcT : callee.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hct]; simp only [evalHOLExact] at htv; rw [← ht2]; exact htv.symm
  have hfl := (find_leaf_ret (callEntryStateHOLFinite s2 callee) tw hcT S hroot htree).run lv
    (by rw [hrun])
  rw [hrun] at hfl
  obtain ⟨lw, rfl, hlwS, hfr⟩ := hfl
  have hpost : { fpost with locals := s2.locals } =
      NS s s2.locals s.globals s.memory fpost.clock := by
    unfold LocFrame at hfr
    dsimp only at hfr
    rw [hfr]; rfl
  rw [hpost]
  show Ret (NS s (s2.locals.update (ofString "leaf", .val (.word lw))) s.globals s.memory
    fpost.clock) _ _
  apply Ret.seq_ite
  intro c hc
  refine ⟨fun _ => ?_, fun hc0 => ?_⟩
  · apply Ret.seq_return
    intro _ _
    right; rfl
  apply Ret.seq_skip
  apply Ret.ns_dec
  intro kyv _
  apply Ret.decCall_gen
  intro values2 body2 callee2 ret2 ev2 mpost hargs2 hlk2 hrun2
  have hsame2 := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "memeq") _ _
    body2 _ ret2 values2 callee2 (by rw [hcode]; exact lookup_memeq') hlk2
  subst hsame2
  have hfr2 := locFrameW_eval _ memeq_locOnlyW (callEntryStateHOLFinite
    (NS s ((s2.locals.update (ofString "leaf", .val (.word lw))).update (ofString "keys", kyv))
      s.globals s.memory fpost.clock) callee2)
  rw [hrun2] at hfr2
  have hpost2 : { mpost with locals := ((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)) } = NS s ((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)) s.globals s.memory mpost.clock := by
    unfold LocFrame at hfr2
    dsimp only at hfr2
    rw [hfr2]; rfl
  simp only [NS_locals]
  rw [hpost2]
  show Ret (NS s (((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)).update (ofString "eq", ev2)) s.globals s.memory mpost.clock) _ _
  apply Ret.seq_ite
  intro c2 hc2
  refine ⟨fun _ => ?_, fun hc20 => ?_⟩
  · apply Ret.seq_return
    intro _ _
    right; rfl
  apply Ret.seq_skip
  -- the delete path
  have hlw0 : lw ≠ 0 := by
    obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
    simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at ha hb
    subst ha hb hc0
    intro h; subst h
    simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
  set L3 := (((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)).update (ofString "eq", ev2)) with hL3
  have hL3t : L3.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hL3, HolFiniteMapExact.lookup_update, FUPDATE, ht2]
  have hL3l : L3.lookup (ofString "leaf") = some (.val (.word lw)) := by
    simp [hL3, HolFiniteMapExact.lookup_update, FUPDATE]
  apply Ret.ns_dec
  intro ndv hndv
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40 (by simpa using hL3t) ndv hndv
  simp only [NS_memory, hnd]
  apply Ret.ns_dec
  intro posv hposv
  obtain ⟨_, rfl⟩ := ev_idx_load _ (ofString "nodes") (ofString "leaf") nd lw 32 16
    (by simp [HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hL3l]) posv hposv
  rcases hpw : s.memory (nd + lw * 32 + 16) with ⟨pw⟩
  have hpwN := hpos lw hlwS hlw0 pw hpw
  apply Ret.ns_dec
  intro cv hcv
  have hcv' : cv = .val (.word (cntw - 1)) := by
    refine ev_field_sub1 _ (ofString "t") tw 24 cntw ?_ ?_ cv hcv
    · simp [HolFiniteMapExact.lookup_update, FUPDATE, hL3t]
    · exact hcnt
  subst hcv'
  simp only [NS_memory, hpw]
  -- bounds
  have hcnt1' := hcnt1 lw hlwS hlw0
  have hlwN : lw.toNat < Nn := hSN _ hlwS
  have htnt : locN s "t" = tw.toNat := by simp [locN, ht]
  have hkey : ∀ (x : PanSemStateFiniteExact 64 F) (u : BitVec 64), x.memory (tw + 24) = .word u →
      hdr x tw.toNat 3 = u.toNat := by
    intro x u hx
    unfold hdr memW
    rw [show tw.toNat + 8 * 3 = tw.toNat + 24 by omega, ofNat_add_toNat']
    rw [show BitVec.ofNat 64 24 = (24 : BitVec 64) from rfl, hx]
  have hfinal : ∀ (t : PanSemStateFiniteExact 64 F), t.memory (tw + 24) = .word (cntw - 1) →
      HtabDelProgress s t := by
    intro t ht24
    left
    rw [htnt, hkey t _ ht24, hkey s _ hcnt,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp; omega
  set Lc := ((L3.update (ofString "nodes", .val (.word nd))).update (ofString "pos", .val (.word pw))).update
    (ofString "count", .val (.word (cntw - 1))) with hLc
  have hLct : Lc.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE, hL3t]
  have hLcn : Lc.lookup (ofString "nodes") = some (.val (.word nd)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  have hLcl : Lc.lookup (ofString "leaf") = some (.val (.word lw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE, hL3l]
  have hLcc : Lc.lookup (ofString "count") = some (.val (.word (cntw - 1))) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  have hLcp : Lc.lookup (ofString "pos") = some (.val (.word pw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  apply Ret.seq_ite
  intro c hc
  refine ⟨fun hcne => ?_, fun hc0 => ?_⟩
  · -- pos ≠ count: move the last leaf into the vacated order slot
    apply Ret.seq_flw
    · exact NoRet.dec' (NoRet.dec' (NoRet.seq NoRet.store' NoRet.store'))
    apply Flw.dec
    intro ov hov
    obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 48 (by simpa using hLct) ov hov
    simp only [NS_memory, how]
    apply Flw.dec
    intro mvv hmvv
    obtain ⟨_, rfl⟩ := ev_idx2_load _ _ _ ow (cntw - 1) 8
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcc]) mvv hmvv
    simp only [NS_memory]
    rcases hmv0 : s.memory (ow + (cntw - 1) * 8) with ⟨mv⟩
    have hmv0' : s.memory (ow + (cntw - 1#64) * 8#64) = .word mv := hmv0
    obtain ⟨hmvN, hmvL⟩ := hmv lw hlwS hlw0 mv hmv0
    apply Flw.seq
    apply Flw.storeW (ow + pw * 8) mv
      (ev_idx2_addr _ _ _ ow pw 8 (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcp]))
      (ev_var _ _ _ (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmv0']))
    intro _
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.storeW (nd + mv * 32 + 16) pw
      (ev_idx_addr _ _ _ nd mv 32 16 (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcn])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmv0']))
      (ev_var _ _ _ (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcp]))
    intro _ _
    have hmvl := mv.isLt
    have hpwl := pw.isLt
    have htwl := tw.isLt
    have hndl := nd.isLt
    have howl := ow.isLt
    have hlwl := lw.isLt
    set M' := updW (updW s.memory (ow + pw * 8) mv) (nd + mv * 32 + 16) pw with hM'
    have hM'r : ∀ x : BitVec 64, x ≠ ow + pw * 8 → x ≠ nd + mv * 32 + 16 → M' x = s.memory x := by
      intro x h1 h2
      rw [hM', updW_ne _ _ _ _ h2, updW_ne _ _ _ _ h1]
    refine Ret.mono (del_rest s _ M' mpost.clock tw nd lw (cntw - 1) rt Nn ?_ ?_ ?_ ?_
      hl1 hl2 hd1 hlwN ?_ ?_) ?_
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLct]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcn]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcl]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcc]
    · rw [hM'r _ (by addr_neq) (by addr_neq)]; exact hrt
    · intro hne p hp
      have hp' : s.memory (nd + lw * 32 + 0) = .word p := by
        rw [← hM'r _ (by addr_neq) (by addr_neq)]; exact hp
      obtain ⟨hpI, hpN, hg, h8, h16⟩ := hpar lw hlwS hlw0 hne p hp'
      have hpl := p.isLt
      have hpmv : p.toNat ≠ mv.toNat := fun h => hLI _ hmvL (h ▸ hpI)
      refine ⟨hpN, fun g hg' => hg g ?_, fun c hc' => h8 c ?_, fun c hc' => h16 c ?_⟩
      · rw [← hM'r _ (by addr_neq) (by addr_neq)]; exact hg'
      · rw [← hM'r _ (by addr_neq) (by addr_neq)]; exact hc'
      · rw [← hM'r _ (by addr_neq) (by addr_neq)]; exact hc'
    · intro v t ht24
      exact hfinal _ ht24
  · subst hc0
    apply Ret.seq_skip
    refine Ret.mono (del_rest s Lc s.memory mpost.clock tw nd lw (cntw - 1) rt Nn hLct hLcn hLcl hLcc
      hl1 hl2 hd1 hlwN hrt ?_) ?_
    · intro hne p hp
      obtain ⟨_, h2, h3, h4, h5⟩ := hpar lw hlwS hlw0 hne p hp
      exact ⟨h2, h3, h4, h5⟩
    · intro v t ht24
      exact hfinal _ ht24


end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelSpec.lean; Opus port from 3ea193df0. -/

/-! `htab_del_progress_spec`: the facts `del_walk` needs, read off `HtabWF`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

theorem nodeF_of {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w u : BitVec 64) (off : Nat)
    (h : x.memory (nd + w * 32 + BitVec.ofNat 64 off) = .word u) :
    nodeF x nd.toNat w.toNat off = u.toNat := by
  unfold nodeF
  rw [memW_node, h]

theorem hdr_of {F : Type} (x : PanSemStateFiniteExact 64 F) (tw u : BitVec 64) (k : Nat)
    (h : x.memory (tw + BitVec.ofNat 64 (8 * k)) = .word u) : hdr x tw.toNat k = u.toNat := by
  unfold hdr memW
  rw [ofNat_add_toNat', h]

theorem nodup_len_le (l : List Nat) (n : Nat) (hnd : l.Nodup) (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) :
    l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

theorem word_eq_zero_of_toNat {w : BitVec 64} (h : w.toNat = 0) : w = 0 := by
  apply BitVec.eq_of_toNat_eq; simpa using h

theorem htab_del_progress_spec_proof : HtabDelProgressSpec := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl, ?_⟩
  intro F s hcode hP _ v hv
  obtain ⟨hAR, hWF, hal⟩ := hP
  -- the table address is a word
  have htpos : 0 < locN s "t" := by
    have := (hWF.1 _ (List.mem_cons_self)).1.1
    simp only [htabFootprint] at this
    have hsb : sourceBase = 2701131776 := rfl
    omega
  obtain ⟨tw, ht, htn⟩ := (fun h => by
    unfold locN at h ⊢
    split at h
    · rename_i w hw; exact ⟨w, hw, rfl⟩
    · omega : 0 < locN s "t" → ∃ w : BitVec 64, s.locals.lookup (ofString "t") = some (.val (.word w)) ∧
        locN s "t" = w.toNat) htpos
  rw [htn] at hWF hal
  obtain ⟨hfp, hdisj, hk1, hk60, hst, hnc, hnx1, hnx, L, I, Fr, hLlen, hnodup, hmemr, hcntI,
    hord, hint, hroot0, hroot1, _, hpar, _, _⟩ := hWF
  -- header words
  rcases hk : s.memory (tw + 0) with ⟨k⟩
  rcases hnd : s.memory (tw + 40) with ⟨nd⟩
  rcases how : s.memory (tw + 48) with ⟨ow⟩
  rcases hcnt : s.memory (tw + 24) with ⟨cntw⟩
  rcases hrt : s.memory (tw + 56) with ⟨rt⟩
  rcases hnc' : s.memory (tw + 80) with ⟨ncw⟩
  rcases hnxt : s.memory (tw + 64) with ⟨nxw⟩
  have e0 : hdr s tw.toNat 0 = k.toNat := hdr_of s tw k 0 hk
  have e3 : hdr s tw.toNat 3 = cntw.toNat := hdr_of s tw cntw 3 hcnt
  have e5 : hdr s tw.toNat 5 = nd.toNat := hdr_of s tw nd 5 hnd
  have e6 : hdr s tw.toNat 6 = ow.toNat := hdr_of s tw ow 6 how
  have e7 : hdr s tw.toNat 7 = rt.toNat := hdr_of s tw rt 7 hrt
  have e8 : hdr s tw.toNat 8 = nxw.toNat := hdr_of s tw nxw 8 hnxt
  have e10 : hdr s tw.toNat 10 = ncw.toNat := hdr_of s tw ncw 10 hnc'
  simp only [e0, e3, e5, e6, e7, e8, e10] at hLlen hcntI hord hint hroot0 hroot1 hpar hmemr hnx hnx1 hk1 hk60 hnc
  set Nn := ncw.toNat + 1 with hNn
  have hLI0 : ∀ n ∈ L ++ I, 1 ≤ n ∧ n < nxw.toNat := fun n hn => (hmemr n).1 (by simp at hn ⊢; tauto)
  have hSN' : ∀ x ∈ L ++ I, x < Nn := fun x hx => by have := hLI0 x hx; omega
  -- block layout
  simp only [htabFootprint, e5, e6, e10] at hfp hdisj
  have hfp0 := (hfp (tw.toNat, 88) (by simp)).1
  have hfp2 := (hfp (nd.toNat, (ncw.toNat + 1) * 32) (by simp)).1
  have hfp3 := (hfp (ow.toNat, (ncw.toNat + 1) * 8) (by simp)).1
  simp only [Inside] at hfp0 hfp2 hfp3
  have hhe : heapEnd < 2 ^ 64 := by decide
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Disj] at hdisj
  have hdA := hdisj.1.2.1
  have hdB := hdisj.1.2.2
  have hdC := hdisj.2.2.1
  have hLnodup : (L ++ I).Nodup := (List.nodup_append.mp hnodup).1
  have hLI : ∀ x ∈ L, x ∉ I := fun x hx hxi =>
    (List.nodup_append.mp hLnodup).2.2 x hx x hxi rfl
  have hLlen' : L.length ≤ nxw.toNat - 1 :=
    nodup_len_le L _ (List.nodup_append.mp hLnodup).1 (fun x hx => hLI0 x (by simp [hx]))
  -- the facts of `del_walk`
  refine (del_walk s hcode tw ht (0 :: (L ++ I)) ?_ ?_ nd ow cntw rt hnd how hcnt hrt Nn
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ L I hLI ?_ ?_ ?_ ?_).run v hv
  · intro u hu
    rw [hrt] at hu
    simp only [HolWordLab.word.injEq] at hu
    subst hu
    by_cases hc : cntw.toNat = 0
    · simp [hroot0 hc]
    · exact List.mem_cons_of_mem _ (hroot1 (by omega)).1
  · intro nd' k' hnd' hk' w hwS hw0 hne
    rw [hnd] at hnd'; rw [hk] at hk'
    simp only [HolWordLab.word.injEq] at hnd' hk'
    subst hnd' hk'
    have hwLI : w.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hw0
      · exact h
    rcases List.mem_append.mp hwLI with hwL | hwI
    · exfalso
      obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwL
      have := (hord i hi).2.1
      rw [hiw] at this
      apply hne
      have hmk : maxKeyLen = 60 := rfl
      have h8 : (k * 8).toNat = k.toNat * 8 := by
        rw [BitVec.toNat_mul]; simp; omega
      rw [h8]
      unfold nodeF at this
      omega
    · obtain ⟨_, h8, h16, _⟩ := hint _ hwI
      unfold nodeF at h8 h16
      exact ⟨List.mem_cons_of_mem _ h8, List.mem_cons_of_mem _ h16⟩
  · intro x hx
    rcases List.mem_cons.mp hx with h | h
    · omega
    · exact hSN' x h
  · intro lw hlwS hlw0
    have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    by_contra hc
    have hc0 : cntw.toNat = 0 := by omega
    rcases hcntI with ⟨_, hI0⟩ | hI1
    · subst hI0
      rw [hc0] at hLlen
      simp [List.length_eq_zero_iff.mp hLlen] at hlwLI
    · omega
  · intro lw hlwS hlw0 u hu
    have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    have hu' := nodeF_of s nd lw u 16 hu
    rcases List.mem_append.mp hlwLI with hwL | hwI
    · obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwL
      have := (hord i hi).2.2
      rw [hiw, hu'] at this
      omega
    · obtain ⟨_, _, h16, _⟩ := hint _ hwI
      rw [hu'] at h16
      exact hSN' _ h16
  · intro lw hlwS hlw0 u hu
    have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    have hc1 : 1 ≤ cntw.toNat := by
      by_contra hc
      have hc0 : cntw.toNat = 0 := by omega
      rcases hcntI with ⟨_, hI0⟩ | hI1
      · subst hI0
        rw [hc0] at hLlen
        simp [List.length_eq_zero_iff.mp hLlen] at hlwLI
      · omega
    have hi : cntw.toNat - 1 < L.length := by omega
    have ho := (hord _ hi).1
    have haddr : ow + (cntw - 1) * 8 = BitVec.ofNat 64 (ow.toNat + 8 * (cntw.toNat - 1)) := by
      rw [ofNat_add_toNat']
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega
    rw [haddr] at hu
    unfold memW at ho
    rw [hu] at ho
    simp only at ho
    rw [ho]
    exact ⟨hSN' _ (List.mem_append_left _ (List.getElem_mem _)), List.getElem_mem _⟩
  · intro lw hlwS hlw0 hlwr p hp
    have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    have hne : lw.toNat ≠ rt.toNat := fun h => hlwr (BitVec.eq_of_toNat_eq h)
    have hp' := nodeF_of s nd lw p 0 hp
    have hpI : p.toNat ∈ I := by rw [← hp']; exact hpar _ hlwLI hne
    have hpLI : p.toNat ∈ L ++ I := List.mem_append_right _ hpI
    obtain ⟨_, h8, h16, _⟩ := hint _ hpI
    refine ⟨hpI, hSN' _ hpLI, ?_, ?_, ?_⟩
    · intro g hg
      have hg' := nodeF_of s nd p g 0 hg
      by_cases hpr : p.toNat = rt.toNat
      · left
        have := (hroot1 (by
          by_contra hc
          rcases hcntI with ⟨_, hI0⟩ | hI1
          · subst hI0; simp at hpI
          · omega)).2
        rw [← hpr, hg'] at this
        exact word_eq_zero_of_toNat this
      · right
        have := hpar _ hpLI hpr
        rw [hg'] at this
        exact hSN' _ (List.mem_append_right _ this)
    · intro c hc
      rw [nodeF_of s nd p c 8 hc] at h8
      exact hSN' _ h8
    · intro c hc
      rw [nodeF_of s nd p c 16 hc] at h16
      exact hSN' _ h16

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelFull.lean; Opus port from 3ea193df0. -/

/-! Memory-exact versions of the deletion tail (`htab_del_spec`): the final memory of a
deleting run of `htab_del`, as an explicit chain of word stores. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-- The post-state of a run that only changed the locals, the clock and the memory. -/
def MemPost {F : Type} (s : PanSemStateFiniteExact 64 F) (M : BitVec 64 → HolWordLab 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat), post = NS s L s.globals M C

theorem MemPost.locals {F : Type} {s : PanSemStateFiniteExact 64 F} {M : BitVec 64 → HolWordLab 64}
    {post : PanSemStateFiniteExact 64 F} (h : MemPost s M post) (L' : HolFiniteMapExact MlS (ValueHOL 64)) :
    MemPost s M { post with locals := L' } := by
  obtain ⟨L, C, rfl⟩ := h
  exact ⟨L', C, rfl⟩

attribute [local irreducible] Ret in
theorem del_tail2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw fr : BitVec 64)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hfr : M (tw + 72) = .word fr) :
    Ret (NS s L s.globals M C)
      (.seq (.store (.op .add [.var .local (ofString "nodes"),
          .panop .mul [.var .local (ofString "leaf"), .const 32], .const 0])
          (.load .one (.op .add [.var .local (ofString "t"), .const 72])))
        (.seq (.store (.op .add [.var .local (ofString "t"), .const 72]) (.var .local (ofString "leaf")))
          (.return (.const 1))))
      (fun _ post => MemPost s (updW (updW M (nd + lw * 32 + 0) fr) (tw + 72) lw) post) := by
  apply Ret.ns_storeV (fun v h => ev_load_word _ _ v h)
  intro a1 w1 hd1 he1 _
  rw [ev_idx_addr _ _ _ nd lw 32 0 hLn hLl] at hd1
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd1
  subst hd1
  obtain ⟨_, hv⟩ := ev_field_load _ (ofString "t") tw 72 hLt _ he1
  simp only [NS_memory, hfr, ValueHOL.val.injEq, HolWordLab.word.injEq] at hv
  subst hv
  apply Ret.ns_storeW (tw + 72) lw (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLl)
  intro _
  apply Ret.ns_ret
  intro _ _
  exact ⟨_, _, rfl⟩

/-- The word of a memory cell. -/
def wv (x : HolWordLab 64) : BitVec 64 := match x with | .word w => w

@[simp] theorem wv_word (w : BitVec 64) : wv (.word w) = w := rfl

/-- Memory after the non-root splice: `s.parent := g`, `g`'s child (or the root) `:= s`,
`p` pushed on the free list. -/
def delSplice (M : BitVec 64 → HolWordLab 64) (tw nd p0 g0 sv : BitVec 64) :
    BitVec 64 → HolWordLab 64 :=
  let M2 := updW M (nd + sv * 32 + 0) g0
  let M3 := if g0 = 0 then updW M2 (tw + 56) sv
    else if wv (M2 (nd + g0 * 32 + 8)) = p0 then updW M2 (nd + g0 * 32 + 8) sv
    else updW M2 (nd + g0 * 32 + 16) sv
  updW (updW M3 (nd + p0 * 32 + 0) (wv (M3 (tw + 72)))) (tw + 72) p0

attribute [local irreducible] Ret Flw in
theorem del_rest3_2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw p0 g0 sv : BitVec 64)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hLp : L.lookup (ofString "p") = some (.val (.word p0)))
    (hLg : L.lookup (ofString "g") = some (.val (.word g0)))
    (hLs : L.lookup (ofString "s") = some (.val (.word sv))) :
    Flw (NS s L s.globals M C) delRest3 (fun r t => r = none →
      t.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      t.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
      t.locals.lookup (ofString "leaf") = some (.val (.word lw)) ∧
      MemPost s (delSplice M tw nd p0 g0 sv) t) := by
  unfold delRest3
  apply Flw.seq
  apply Flw.storeW (nd + sv * 32 + 0) g0 (ev_idx_addr _ _ _ nd sv 32 0 hLn hLs) (ev_var _ _ _ hLg)
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  apply Flw.seq
  apply Flw.ite
  intro c hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
  simp [evalAt, evalHOLExact, hLg] at ha hb
  subst ha hb
  refine ⟨fun hc1 => ?_, fun hc0 => ?_⟩
  · have hg0 : g0 = 0 := by
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
      split at hcw
      · assumption
      · exact absurd hcw hc1
    apply Flw.storeW (tw + 56) sv (ev_fld_addr _ _ tw 56 hLt) (ev_var _ _ _ hLs)
    intro _
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.seq
    apply Flw.storeV (fun v h => ev_load_word _ _ v h)
    intro a1 w1 hd1' he1 _
    obtain rfl := ev_idx_addr_eq _ _ _ nd p0 32 0 a1 hd1' (by simpa using hLn) (by simpa using hLp)
    obtain ⟨_, hv⟩ := ev_field_load _ (ofString "t") tw 72 (by simpa using hLt) _ he1
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.storeW (tw + 72) p0 (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLp)
    intro _ _
    refine ⟨hLt, hLn, hLl, L, C, ?_⟩
    simp only [NS_memory] at hv
    have hw1 : w1 = wv (updW (updW M (nd + sv * 32 + 0) g0) (tw + 56) sv (tw + 72)) := by
      simp only [ValueHOL.val.injEq] at hv; rw [← hv]; rfl
    rw [hw1]
    simp only [delSplice, if_pos hg0]
    rfl
  · have hg0 : g0 ≠ 0 := by
      intro h; subst h hc0
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    apply Flw.ite
    intro c2 hc2
    obtain ⟨a2, b2, ha2, hb2, hcw2⟩ := evalAt_cmp _ .equal _ _ c2 hc2
    simp [evalAt, evalHOLExact, hLp] at hb2
    subst hb2
    obtain ⟨_, hv2⟩ := ev_idx_load _ _ _ nd g0 32 8 (by simpa using hLn) (by simpa using hLg) _ ha2
    simp only [NS_memory, ValueHOL.val.injEq] at hv2
    have hwa2 : wv (updW M (nd + sv * 32 + 0) g0 (nd + g0 * 32 + 8)) = a2 := by rw [← hv2]; rfl
    refine ⟨fun hc21 => ?_, fun hc20 => ?_⟩
    · have hap : a2 = p0 := by
        simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw2
        split at hcw2
        · assumption
        · exact absurd hcw2 hc21
      apply Flw.storeW (nd + g0 * 32 + 8) sv (ev_idx_addr _ _ _ nd g0 32 8 hLn hLg) (ev_var _ _ _ hLs)
      intro _
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.seq
      apply Flw.storeV (fun v h => ev_load_word _ _ v h)
      intro a1 w1 hd1' he1 _
      obtain rfl := ev_idx_addr_eq _ _ _ nd p0 32 0 a1 hd1' (by simpa using hLn) (by simpa using hLp)
      obtain ⟨_, hv⟩ := ev_field_load _ (ofString "t") tw 72 (by simpa using hLt) _ he1
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.storeW (tw + 72) p0 (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLp)
      intro _ _
      refine ⟨hLt, hLn, hLl, L, C, ?_⟩
      simp only [NS_memory] at hv
      have hw1 : w1 = wv (updW (updW M (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 8) sv (tw + 72)) := by
        simp only [ValueHOL.val.injEq] at hv; rw [← hv]; rfl
      rw [hw1]
      simp only [delSplice, if_neg hg0, hwa2, hap, if_pos rfl]
      rfl
    · have hap : a2 ≠ p0 := by
        intro h; subst h hc20
        simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw2
      apply Flw.storeW (nd + g0 * 32 + 16) sv (ev_idx_addr _ _ _ nd g0 32 16 hLn hLg) (ev_var _ _ _ hLs)
      intro _
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.seq
      apply Flw.storeV (fun v h => ev_load_word _ _ v h)
      intro a1 w1 hd1' he1 _
      obtain rfl := ev_idx_addr_eq _ _ _ nd p0 32 0 a1 hd1' (by simpa using hLn) (by simpa using hLp)
      obtain ⟨_, hv⟩ := ev_field_load _ (ofString "t") tw 72 (by simpa using hLt) _ he1
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply Flw.storeW (tw + 72) p0 (ev_fld_addr _ _ tw 72 hLt) (ev_var _ _ _ hLp)
      intro _ _
      refine ⟨hLt, hLn, hLl, L, C, ?_⟩
      simp only [NS_memory] at hv
      have hw1 : w1 = wv (updW (updW M (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 16) sv (tw + 72)) := by
        simp only [ValueHOL.val.injEq] at hv; rw [← hv]; rfl
      rw [hw1]
      simp only [delSplice, if_neg hg0, hwa2, if_neg hap]
      rfl

theorem delSplice_72 (M : BitVec 64 → HolWordLab 64) (tw nd p0 g0 sv : BitVec 64) :
    delSplice M tw nd p0 g0 sv (tw + 72) = .word p0 := by
  simp [delSplice, updW]

/-- The sibling chosen by `htab_del`. -/
def delSib (M : BitVec 64 → HolWordLab 64) (nd p0 lw : BitVec 64) : BitVec 64 :=
  if wv (M (nd + p0 * 32 + 8)) = lw then wv (M (nd + p0 * 32 + 16)) else wv (M (nd + p0 * 32 + 8))

/-- Final memory of the deletion tail, from the memory `M` before `st t+24, count`. -/
def DelPostR {F : Type} (s : PanSemStateFiniteExact 64 F) (M : BitVec 64 → HolWordLab 64)
    (tw nd lw cw : BitVec 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  (wv (updW M (tw + 24) cw (tw + 56)) = lw ∧
    MemPost s (updW (updW (updW (updW M (tw + 24) cw) (tw + 56) 0) (nd + lw * 32 + 0)
      (wv (updW M (tw + 24) cw (tw + 72)))) (tw + 72) lw) post) ∨
  (wv (updW M (tw + 24) cw (tw + 56)) ≠ lw ∧
    MemPost s (updW (updW (delSplice (updW M (tw + 24) cw) tw nd
        (wv (updW M (tw + 24) cw (nd + lw * 32 + 0)))
        (wv (updW M (tw + 24) cw (nd + wv (updW M (tw + 24) cw (nd + lw * 32 + 0)) * 32 + 0)))
        (delSib (updW M (tw + 24) cw) nd (wv (updW M (tw + 24) cw (nd + lw * 32 + 0))) lw))
      (nd + lw * 32 + 0) (wv (updW M (tw + 24) cw (nd + lw * 32 + 0)))) (tw + 72) lw) post)

attribute [local irreducible] Ret Flw in
theorem del_rest2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (tw nd lw cw : BitVec 64)
    (hLt : L.lookup (ofString "t") = some (.val (.word tw)))
    (hLn : L.lookup (ofString "nodes") = some (.val (.word nd)))
    (hLl : L.lookup (ofString "leaf") = some (.val (.word lw)))
    (hLc : L.lookup (ofString "count") = some (.val (.word cw))) :
    Ret (NS s L s.globals M C) delRest (fun _ post => DelPostR s M tw nd lw cw post) := by
  unfold delRest
  apply Ret.ns_storeW (tw + 24) cw (ev_fld_addr _ _ tw 24 hLt) (ev_var _ _ _ hLc)
  intro _
  set M1 := updW M (tw + 24) cw with hM1
  apply Ret.seq_ite
  intro c hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
  have ha' : a = lw := by
    simp [evalAt, evalHOLExact, hLl] at ha; exact ha.symm
  have hb' : wv (M1 (tw + 56)) = b := by
    obtain ⟨_, hbv⟩ := ev_field_load (NS s L s.globals M1 C) _ tw 56 hLt _ hb
    simp only [NS_memory, ValueHOL.val.injEq] at hbv
    rw [← hbv]; rfl
  subst ha'
  refine ⟨fun hc1 => ?_, fun hc0 => ?_⟩
  · have hab : a = b := by
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
      split at hcw
      · assumption
      · exact absurd hcw hc1
    apply Ret.ns_storeW (tw + 56) 0 (ev_fld_addr _ _ tw 56 hLt) (by simp [ev, evalHOLExact])
    intro _
    rcases hfr : M1 (tw + 72) with ⟨fr⟩
    refine Ret.mono (del_tail2 s L _ C tw nd a fr hLt hLn hLl
      (by rw [updW_ne _ _ _ _ (fun h => absurd ((BitVec.add_right_inj tw).mp h) (by decide))]; exact hfr)) ?_
    intro v t ht
    left
    refine ⟨by rw [hb', hab], ?_⟩
    have hfr' : updW M (tw + 24) cw (tw + 72) = .word fr := hfr
    rw [hfr', wv_word]; exact ht
  · have hne : wv (M1 (tw + 56)) ≠ a := by
      rw [hb']
      intro h; subst h; subst hc0
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    apply Ret.seq_flw
    · exact NoRet.dec' (NoRet.dec' (NoRet.dec' (NoRet.seq (NoRet.ite NoRet.assign NoRet.skip)
        (NoRet.seq NoRet.store' (NoRet.seq (NoRet.ite NoRet.store' (NoRet.ite NoRet.store' NoRet.store'))
          (NoRet.seq NoRet.store' NoRet.store'))))))
    apply Flw.dec
    intro pv hpv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd a 32 0 (by simpa using hLn) (by simpa using hLl) pv hpv
    simp only [NS_memory]
    rcases hp0 : M1 (nd + a * 32 + 0) with ⟨p0⟩
    show Flw (NS s (L.update (ofString "p", .val (.word p0))) s.globals M1 C) _ _
    apply Flw.dec
    intro gv hgv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 0
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hLn])
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE]) gv hgv
    simp only [NS_memory]
    rcases hg0 : M1 (nd + p0 * 32 + 0) with ⟨g0⟩
    show Flw (NS s ((L.update (ofString "p", .val (.word p0))).update (ofString "g", .val (.word g0)))
      s.globals M1 C) _ _
    apply Flw.dec
    intro sv hsv
    obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 8
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hLn])
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE]) sv hsv
    simp only [NS_memory]
    rcases hs0 : M1 (nd + p0 * 32 + 8) with ⟨s0⟩
    set L5 := ((L.update (ofString "p", .val (.word p0))).update (ofString "g", .val (.word g0))).update
      (ofString "s", .val (.word s0)) with hL5
    have hL5t : L5.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLt]
    have hL5n : L5.lookup (ofString "nodes") = some (.val (.word nd)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLn]
    have hL5l : L5.lookup (ofString "leaf") = some (.val (.word a)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE, hLl]
    have hL5p : L5.lookup (ofString "p") = some (.val (.word p0)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE]
    have hL5g : L5.lookup (ofString "g") = some (.val (.word g0)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE]
    have hL5s : L5.lookup (ofString "s") = some (.val (.word s0)) := by
      simp [hL5, HolFiniteMapExact.lookup_update, FUPDATE]
    show Flw (NS s L5 s.globals M1 C) _ _
    apply Flw.seq
    apply Flw.ite
    intro c3 hc3
    obtain ⟨a3, b3, ha3, hb3, hcw3⟩ := evalAt_cmp _ .equal _ _ c3 hc3
    simp [evalAt, evalHOLExact, hL5s] at ha3
    simp [evalAt, evalHOLExact, hL5l] at hb3
    subst ha3 hb3
    refine ⟨fun hc31 => ?_, fun hc30 => ?_⟩
    · have hsl : s0 = a := by
        simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw3
        split at hcw3
        · assumption
        · exact absurd hcw3 hc31
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_idx_load _ _ _ nd p0 32 16 hL5n hL5p v hv
      simp only [NS_memory]
      rcases hs1 : M1 (nd + p0 * 32 + 16) with ⟨s1⟩
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      refine Flw.mono (del_rest3_2 s _ M1 C tw nd a p0 g0 s1
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5t])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5n])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5l])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5p])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hL5g])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])) ?_
      intro r t hQ hr
      obtain ⟨h1, h2, h3, L', C', rfl⟩ := hQ hr
      refine Ret.mono (del_tail2 s _ _ C' tw nd a p0
        (by simp only [NS_locals] at h1; simp [PanRunBounded.resVarEq_lookup, h1])
        (by simp only [NS_locals] at h2; simp [PanRunBounded.resVarEq_lookup, h2])
        (by simp only [NS_locals] at h3; simp [PanRunBounded.resVarEq_lookup, h3])
        (delSplice_72 _ _ _ _ _ _)) ?_
      intro w t' ht'
      right
      refine ⟨hne, ?_⟩
      have hsib : delSib M1 nd p0 a = s1 := by
        simp only [delSib, hs0, hs1, wv_word, hsl, if_pos rfl, if_true]
      have hp0' : updW M (tw + 24) cw (nd + a * 32 + 0) = .word p0 := hp0
      have hg0' : updW M (tw + 24) cw (nd + p0 * 32 + 0) = .word g0 := hg0
      have hsib' : delSib (updW M (tw + 24) cw) nd p0 a = _ := hsib
      rw [hp0', wv_word, hg0', wv_word, hsib']
      exact ht'.locals _ |>.locals _ |>.locals _
    · have hsl : s0 ≠ a := by
        intro h; subst h hc30
        simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw3
      apply Flw.skip
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      refine Flw.mono (del_rest3_2 s _ M1 C tw nd a p0 g0 s0 hL5t hL5n hL5l hL5p hL5g hL5s) ?_
      intro r t hQ hr
      obtain ⟨h1, h2, h3, L', C', rfl⟩ := hQ hr
      refine Ret.mono (del_tail2 s _ _ C' tw nd a p0
        (by simp only [NS_locals] at h1; simp [PanRunBounded.resVarEq_lookup, h1])
        (by simp only [NS_locals] at h2; simp [PanRunBounded.resVarEq_lookup, h2])
        (by simp only [NS_locals] at h3; simp [PanRunBounded.resVarEq_lookup, h3])
        (delSplice_72 _ _ _ _ _ _)) ?_
      intro w t' ht'
      right
      refine ⟨hne, ?_⟩
      have hsib : delSib M1 nd p0 a = s0 := by
        simp only [delSib, hs0, wv_word, if_neg hsl]
      have hp0' : updW M (tw + 24) cw (nd + a * 32 + 0) = .word p0 := hp0
      have hg0' : updW M (tw + 24) cw (nd + p0 * 32 + 0) = .word g0 := hg0
      have hsib' : delSib (updW M (tw + 24) cw) nd p0 a = _ := hsib
      rw [hp0', wv_word, hg0', wv_word, hsib']
      exact ht'.locals _ |>.locals _ |>.locals _

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelWalk2.lean; Opus port from 3ea193df0. -/

/-! `htab_del` with its exact final memory: either an early exit (only locals and clock change)
or a deletion of a found leaf `lw`, ending in `DelPostR` over the memory after the order-slot
move. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-- The outcome of a normal return of `htab_del`. -/
def DelOut {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (tw nd ow cntw : BitVec 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post = { s with locals := post.locals, clock := post.clock } ∨
  ∃ lw pw mv : BitVec 64, lw.toNat ∈ S ∧ lw ≠ 0 ∧
    (∀ nd k : BitVec 64, s.memory (tw + 40) = .word nd → s.memory (tw + 0) = .word k →
      memW s (nd.toNat + 32 * lw.toNat + 24) = (k * 8).toNat) ∧
    s.memory (nd + lw * 32 + 16) = .word pw ∧ s.memory (ow + (cntw - 1) * 8) = .word mv ∧
    ((pw = cntw - 1 ∧ DelPostR s s.memory tw nd lw (cntw - 1) post) ∨
     (pw ≠ cntw - 1 ∧ DelPostR s (updW (updW s.memory (ow + pw * 8) mv) (nd + mv * 32 + 16) pw)
        tw nd lw (cntw - 1) post))

theorem DelPostR.locals {F : Type} {s : PanSemStateFiniteExact 64 F} {M : BitVec 64 → HolWordLab 64}
    {tw nd lw cw : BitVec 64} {post : PanSemStateFiniteExact 64 F} (h : DelPostR s M tw nd lw cw post)
    (L' : HolFiniteMapExact MlS (ValueHOL 64)) : DelPostR s M tw nd lw cw { post with locals := L' } := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2.locals _⟩
  · exact Or.inr ⟨h1, h2.locals _⟩

attribute [local irreducible] Ret Flw in
theorem del_walk2 {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (tw : BitVec 64) (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, s.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, s.memory (tw + 40) = .word nd → s.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW s (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW s (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW s (nd.toNat + 32 * w.toNat + 16) ∈ S)
    (nd ow cntw : BitVec 64) (hnd : s.memory (tw + 40) = .word nd)
    (how : s.memory (tw + 48) = .word ow) (hcnt : s.memory (tw + 24) = .word cntw) :
    Ret s (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_del).body)
      (fun _ post => DelOut s S tw nd ow cntw post) := by
  htab_unfold Guest.Software.guestFn_htab_del
  apply Ret.dec
  intro klv hklv
  apply Ret.dec
  intro stv hstv
  set s2 := setVarHOLFinite (ofString "stride") stv (setVarHOLFinite (ofString "klen") klv s)
    with hs2
  have ht2 : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]
  apply Ret.decCall_gen
  intro values body callee ret lv fpost hargs hl hrun
  have hlook := lookup_find_leaf'
  have hsame := lookupCodeHOLFinite_installed_body s2.code.lookup (ofString "htab_find_leaf") _ _
    body _ ret values callee (by rw [show s2.code = s.code from rfl, hcode]; exact hlook) hl
  subst hsame
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s2 _ _ hargs
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s2.code.lookup (ofString "htab_find_leaf") []
    (ofString "t") .one [(ofString "key", .one)] _ _ (by simp)
    (by rw [show s2.code = s.code from rfl, hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hcT : callee.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hct]; simp only [evalHOLExact] at htv; rw [← ht2]; exact htv.symm
  have hfl := (find_leaf_ret2 (callEntryStateHOLFinite s2 callee) tw hcT S hroot htree).run lv
    (by rw [hrun])
  rw [hrun] at hfl
  obtain ⟨lw, rfl, hlwS, hfr, hcrit⟩ := hfl
  have hpost : { fpost with locals := s2.locals } =
      NS s s2.locals s.globals s.memory fpost.clock := by
    unfold LocFrame at hfr
    dsimp only at hfr
    rw [hfr]; rfl
  rw [hpost]
  show Ret (NS s (s2.locals.update (ofString "leaf", .val (.word lw))) s.globals s.memory
    fpost.clock) _ _
  apply Ret.seq_ite
  intro c hc
  refine ⟨fun _ => ?_, fun hc0 => ?_⟩
  · apply Ret.seq_return
    intro _ _
    left; rfl
  apply Ret.seq_skip
  apply Ret.ns_dec
  intro kyv _
  apply Ret.decCall_gen
  intro values2 body2 callee2 ret2 ev2 mpost hargs2 hlk2 hrun2
  have hsame2 := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "memeq") _ _
    body2 _ ret2 values2 callee2 (by rw [hcode]; exact lookup_memeq') hlk2
  subst hsame2
  have hfr2 := locFrameW_eval _ memeq_locOnlyW (callEntryStateHOLFinite
    (NS s ((s2.locals.update (ofString "leaf", .val (.word lw))).update (ofString "keys", kyv))
      s.globals s.memory fpost.clock) callee2)
  rw [hrun2] at hfr2
  have hpost2 : { mpost with locals := ((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)) } = NS s ((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)) s.globals s.memory mpost.clock := by
    unfold LocFrame at hfr2
    dsimp only at hfr2
    rw [hfr2]; rfl
  simp only [NS_locals]
  rw [hpost2]
  show Ret (NS s (((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)).update (ofString "eq", ev2)) s.globals s.memory mpost.clock) _ _
  apply Ret.seq_ite
  intro c2 hc2
  refine ⟨fun _ => ?_, fun hc20 => ?_⟩
  · apply Ret.seq_return
    intro _ _
    left; rfl
  apply Ret.seq_skip
  -- the delete path
  have hlw0 : lw ≠ 0 := by
    obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
    simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at ha hb
    subst ha hb hc0
    intro h; subst h
    simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
  set L3 := (((s2.locals.update (ofString "leaf", .val (.word lw))).update
      (ofString "keys", kyv)).update (ofString "eq", ev2)) with hL3
  have hL3t : L3.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hL3, HolFiniteMapExact.lookup_update, FUPDATE, ht2]
  have hL3l : L3.lookup (ofString "leaf") = some (.val (.word lw)) := by
    simp [hL3, HolFiniteMapExact.lookup_update, FUPDATE]
  apply Ret.ns_dec
  intro ndv hndv
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40 (by simpa using hL3t) ndv hndv
  simp only [NS_memory, hnd]
  apply Ret.ns_dec
  intro posv hposv
  obtain ⟨_, rfl⟩ := ev_idx_load _ (ofString "nodes") (ofString "leaf") nd lw 32 16
    (by simp [HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [HolFiniteMapExact.lookup_update, FUPDATE, hL3l]) posv hposv
  rcases hpw : s.memory (nd + lw * 32 + 16) with ⟨pw⟩
  apply Ret.ns_dec
  intro cv hcv
  have hcv' : cv = .val (.word (cntw - 1)) := by
    refine ev_field_sub1 _ (ofString "t") tw 24 cntw ?_ ?_ cv hcv
    · simp [HolFiniteMapExact.lookup_update, FUPDATE, hL3t]
    · exact hcnt
  subst hcv'
  simp only [NS_memory, hpw]
  set Lc := ((L3.update (ofString "nodes", .val (.word nd))).update (ofString "pos", .val (.word pw))).update
    (ofString "count", .val (.word (cntw - 1))) with hLc
  have hLct : Lc.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE, hL3t]
  have hLcn : Lc.lookup (ofString "nodes") = some (.val (.word nd)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  have hLcl : Lc.lookup (ofString "leaf") = some (.val (.word lw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE, hL3l]
  have hLcc : Lc.lookup (ofString "count") = some (.val (.word (cntw - 1))) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  have hLcp : Lc.lookup (ofString "pos") = some (.val (.word pw)) := by
    simp [hLc, HolFiniteMapExact.lookup_update, FUPDATE]
  apply Ret.seq_ite
  intro c hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .notEqual _ _ c hc
  simp [evalAt, evalHOLExact, hLcp] at ha
  simp [evalAt, evalHOLExact, hLcc] at hb
  subst ha hb
  rcases hmv0 : s.memory (ow + (cntw - 1) * 8) with ⟨mv⟩
  have hmv0' : s.memory (ow + (cntw - 1#64) * 8#64) = .word mv := hmv0
  refine ⟨fun hcne => ?_, fun hc0 => ?_⟩
  · -- pos ≠ count: move the last leaf into the vacated order slot
    have hne : pw ≠ cntw - 1 := by
      intro h; rw [h] at hcw
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
      exact hcne hcw
    apply Ret.seq_flw
    · exact NoRet.dec' (NoRet.dec' (NoRet.seq NoRet.store' NoRet.store'))
    apply Flw.dec
    intro ov hov
    obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 48 (by simpa using hLct) ov hov
    simp only [NS_memory, how]
    apply Flw.dec
    intro mvv hmvv
    obtain ⟨_, rfl⟩ := ev_idx2_load _ _ _ ow (cntw - 1) 8
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcc]) mvv hmvv
    simp only [NS_memory]
    apply Flw.seq
    apply Flw.storeW (ow + pw * 8) mv
      (ev_idx2_addr _ _ _ ow pw 8 (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcp]))
      (ev_var _ _ _ (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmv0']))
    intro _
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.storeW (nd + mv * 32 + 16) pw
      (ev_idx_addr _ _ _ nd mv 32 16 (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcn])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmv0']))
      (ev_var _ _ _ (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hLcp]))
    intro _ _
    refine Ret.mono (del_rest2 s _ (updW (updW s.memory (ow + pw * 8) mv) (nd + mv * 32 + 16) pw)
      mpost.clock tw nd lw (cntw - 1) ?_ ?_ ?_ ?_) ?_
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLct]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcn]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcl]
    · simp [setVarHOLFinite, PanRunBounded.resVarEq_lookup, HolFiniteMapExact.lookup_update, FUPDATE,
        hLcc]
    · intro v t ht'
      right
      exact ⟨lw, pw, mv, hlwS, hlw0, hcrit hlw0, hpw, hmv0, Or.inr ⟨hne, ht'.locals _⟩⟩
  · have heq : pw = cntw - 1 := by
      by_contra h
      subst hc0
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
      exact h hcw
    subst hc0
    apply Ret.seq_skip
    refine Ret.mono (del_rest2 s Lc s.memory mpost.clock tw nd lw (cntw - 1) hLct hLcn hLcl hLcc) ?_
    intro v t ht'
    right
    exact ⟨lw, pw, mv, hlwS, hlw0, hcrit hlw0, hpw, hmv0, Or.inl ⟨heq, ht'.locals _⟩⟩

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelBridge.lean; Opus port from 3ea193df0. -/

/-! Bridges for `htab_del_spec`: `HtabWF` as block facts plus the abstract `TreeWF`, the exit
relation for a run that only rewrote memory, and numeric reads `rdN` through word stores. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8HtabAstra

/-- The block part of `HtabWF`. -/
def HtabBlocks {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : Prop :=
  (∀ i ∈ htabFootprint s t, Inside i sourceBase heapEnd ∧ WordsOK s i) ∧
  (htabFootprint s t).Pairwise Disj ∧
  1 ≤ hdr s t 0 ∧ hdr s t 0 ≤ maxKeyLen ∧ hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 ∧
  2 ≤ hdr s t 10 ∧ 1 ≤ hdr s t 8 ∧ hdr s t 8 ≤ hdr s t 10 + 1

theorem freeChain_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat), FreeChain s nodes head Fr ↔ FreeChainF (nodeF s nodes) head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain, FreeChainF, freeChain_iff s nodes rest]

theorem htabWF_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    HtabWF s t ↔ HtabBlocks s t ∧ ∃ L I Fr : List Nat,
      TreeWF L I Fr (hdr s t 8) (hdr s t 0) (hdr s t 3) (hdr s t 7) (hdr s t 9)
        (nodeF s (hdr s t 5)) (fun i => memW s (hdr s t 6 + 8 * i)) := by
  simp only [HtabWF, HtabBlocks, TreeWF, freeChain_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, h⟩
    exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h⟩
  · rintro ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, h⟩

theorem wordAt_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    WordAt s a ↔ s.memaddrs (BitVec.ofNat 64 a) := by
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · intro h
    rcases hm : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
    exact ⟨w, h, hm⟩

theorem blocks_transfer {F : Type} (s s' : PanSemStateFiniteExact 64 F) (t : Nat)
    (hdom : s'.memaddrs = s.memaddrs) (h0 : hdr s' t 0 = hdr s t 0) (h1 : hdr s' t 1 = hdr s t 1)
    (h4 : hdr s' t 4 = hdr s t 4) (h5 : hdr s' t 5 = hdr s t 5) (h6 : hdr s' t 6 = hdr s t 6)
    (h8 : hdr s' t 8 = hdr s t 8) (h10 : hdr s' t 10 = hdr s t 10) (h : HtabBlocks s t) :
    HtabBlocks s' t := by
  have hfp : htabFootprint s' t = htabFootprint s t := by
    simp only [htabFootprint, h1, h4, h5, h6, h10]
  unfold HtabBlocks at h ⊢
  rw [hfp, h0, h1, h8, h10]
  obtain ⟨hA, hB, rest⟩ := h
  refine ⟨fun i hi => ⟨(hA i hi).1, ?_⟩, hB, rest⟩
  obtain ⟨a1, a2, a3⟩ := (hA i hi).2
  refine ⟨a1, a2, fun k hk => ?_⟩
  rw [wordAt_iff, hdom]
  exact (wordAt_iff _ _).1 (a3 k hk)

/-- A run that changed only locals, clock and memory, inside the old footprint. -/
theorem exitR_memPost {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F)
    (M : BitVec 64 → HolWordLab 64) (hP : MemPost s M post) (hA : ArenaReady s)
    (hal : ∀ i ∈ htabFootprint s t, Allocated s i) (hW : HtabWF post t)
    (hfp : htabFootprint post t = htabFootprint s t)
    (hfr : ∀ a : BitVec 64, (∀ i ∈ htabFootprint s t, ¬ InIvl a.toNat i) → M a = s.memory a) :
    ExitR t s post := by
  obtain ⟨L, C, rfl⟩ := hP
  refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩, hW, le_refl _, ?_, fun a ha _ => hfr a (fun i hi hin => ha i hi ⟨by have := hin.1; omega, hin.2⟩),
    fun _ _ => rfl⟩
  intro i hi
  rw [hfp] at hi
  exact ⟨hal i hi, Or.inl ⟨i, hi, le_refl _, le_refl _⟩⟩

/-! ### Numeric reads -/

/-- The word at numeric address `a`, as a number. -/
def rdN (M : BitVec 64 → HolWordLab 64) (a : Nat) : Nat := (wv (M (BitVec.ofNat 64 a))).toNat

theorem rdN_upd (M : BitVec 64 → HolWordLab 64) (b a : Nat) (w : BitVec 64) :
    rdN (updW M (BitVec.ofNat 64 b) w) a = if a % 2 ^ 64 = b % 2 ^ 64 then w.toNat else rdN M a := by
  unfold rdN updW
  by_cases h : a % 2 ^ 64 = b % 2 ^ 64
  · have : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
      apply BitVec.eq_of_toNat_eq; simpa using h
    rw [if_pos h]; simp [this]
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
      intro e; apply h; simpa using congrArg BitVec.toNat e
    rw [if_neg h]; simp [this]

theorem wv_toNat_ofNat (M : BitVec 64 → HolWordLab 64) (b : Nat) :
    (wv (M (BitVec.ofNat 64 b))).toNat = rdN M b := rfl

theorem memW_NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C a : Nat) : memW (NS s L G M C) a = rdN M a := by
  unfold memW rdN NS
  dsimp only
  rcases M (BitVec.ofNat 64 a) with ⟨w⟩
  rfl

theorem memW_rdN {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : memW s a = rdN s.memory a := by
  unfold memW rdN
  rcases s.memory (BitVec.ofNat 64 a) with ⟨w⟩
  rfl

/-! Word addresses as numerals (no side conditions: both sides wrap the same way). -/

theorem an0 (nd i : BitVec 64) : nd + i * 32 + 0 = BitVec.ofNat 64 (nd.toNat + 32 * i.toNat + 0) :=
  (ofNat_node_addr nd i 0).symm
theorem an8 (nd i : BitVec 64) : nd + i * 32 + 8 = BitVec.ofNat 64 (nd.toNat + 32 * i.toNat + 8) :=
  (ofNat_node_addr nd i 8).symm
theorem an16 (nd i : BitVec 64) : nd + i * 32 + 16 = BitVec.ofNat 64 (nd.toNat + 32 * i.toNat + 16) :=
  (ofNat_node_addr nd i 16).symm
theorem ah (t : BitVec 64) (c : Nat) : t + BitVec.ofNat 64 c = BitVec.ofNat 64 (t.toNat + c) :=
  (ofNat_add_toNat' t c).symm
theorem ah24 (t : BitVec 64) : t + 24 = BitVec.ofNat 64 (t.toNat + 24) := ah t 24
theorem ah56 (t : BitVec 64) : t + 56 = BitVec.ofNat 64 (t.toNat + 56) := ah t 56
theorem ah72 (t : BitVec 64) : t + 72 = BitVec.ofNat 64 (t.toNat + 72) := ah t 72
theorem ao8 (o i : BitVec 64) : o + i * 8 = BitVec.ofNat 64 (o.toNat + 8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  omega

end InitECandidate.Solver.Wave8HtabAstra.Htab

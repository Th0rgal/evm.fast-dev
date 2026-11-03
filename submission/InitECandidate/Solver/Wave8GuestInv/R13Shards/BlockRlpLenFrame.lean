import InitECandidate.Solver.Wave8GuestInv.R13Shards.PayloadWorldHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_bytes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_word
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_rlp_encode_bytes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min

/-! Proof that `block_rlp_length(hdr, pl)` preserves `WorldStep (fun _ => []) [] stdKeep NoExtra`
whenever `WorldOK s` and `HeaderAt s (locN s "hdr")` hold!
Even though `wk_block_rlp_length` in `C18.lean` has `HeaderOK` (`HeaderAt s (locN s "h")`) instead
of `HeaderAt s (locN s "hdr")`, `block_rlp_length` is concrete in `originalRuntimeCode`, so we
prove its relational `WorldStep` directly from `originalRuntimeCode` using `M11`/`M13`/`M27`! -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Lookups & `FunLocFrame` for the read-only helpers of `block_rlp_length` -/

theorem lookup_heap_mark_fn :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_heap_release_fn :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

theorem lookup_rlp_header_len_fn :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_rlp_header_len, .one) :=
  lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_header_len) rfl

theorem lookup_rlp_encode_list_header_fn :
    originalRuntimeCode.lookup (ofString "rlp_encode_list_header") =
      some ([(ofString "dst", .one), (ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_list_header, .one) :=
  lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl

theorem lookup_rlp_bytes_encoded_len_fn :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

theorem lookup_rlp_list_header_len_fn :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_header_len, .one) :=
  lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl

theorem lookup_rlp_word_encoded_len_fn :
    originalRuntimeCode.lookup (ofString "rlp_word_encoded_len") =
      some ([(ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len, .one) :=
  lookup_of_guestAst_getElem 127 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_word_encoded_len) rfl

theorem lookup_rlp_put_u256_fn :
    originalRuntimeCode.lookup (ofString "rlp_put_u256") =
      some ([(ofString "dst", .one), (ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_rlp_put_u256, .one) :=
  lookup_of_guestAst_getElem 228 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_u256) rfl

theorem lookup_encode_header_fn :
    originalRuntimeCode.lookup (ofString "encode_header") =
      some ([(ofString "h", .one)],
        sourceFnBody Guest.Software.guestFn_encode_header, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 229 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_header) rfl

theorem lookup_withdrawal_rlp_len_fn :
    originalRuntimeCode.lookup (ofString "withdrawal_rlp_len") =
      some ([(ofString "wd", .one)],
        sourceFnBody Guest.Software.guestFn_withdrawal_rlp_len, .one) :=
  lookup_of_guestAst_getElem 837 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_withdrawal_rlp_len) rfl

theorem lookup_block_rlp_length_params :
    originalRuntimeCode.lookup (ofString "block_rlp_length") =
      some ([(ofString "hdr", .one), (ofString "pl", .one)],
        sourceFnBody Guest.Software.guestFn_block_rlp_length, .one) :=
  lookup_of_guestAst_getElem 862 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_block_rlp_length) rfl

/-! ### `M13.FunLocFrame` instances for read-only RLP length helpers -/

theorem funLocFrame_rlp_be_len : M13.FunLocFrame (ofString "rlp_be_len") :=
  M13.funLocFrame_of_locOnlyW 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len rfl rfl

theorem funLocFrame_rlp_header_len : M13.FunLocFrame (ofString "rlp_header_len") := by
  refine ⟨_, _, _, lookup_rlp_header_len_fn, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) funLocFrame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem funLocFrame_rlp_list_header_len : M13.FunLocFrame (ofString "rlp_list_header_len") := by
  refine ⟨_, _, _, lookup_rlp_list_header_len_fn, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact M13.locFrame_tailCall hcode funLocFrame_rlp_header_len _

theorem funLocFrame_rlp_bytes_encoded_len : M13.FunLocFrame (ofString "rlp_bytes_encoded_len") := by
  refine ⟨_, _, _, lookup_rlp_bytes_encoded_len_fn, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_bytes_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) funLocFrame_rlp_header_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem funLocFrame_rlp_word_encoded_len : M13.FunLocFrame (ofString "rlp_word_encoded_len") := by
  refine ⟨_, _, _, lookup_rlp_word_encoded_len_fn, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) funLocFrame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem funLocFrame_withdrawal_rlp_len : M13.FunLocFrame (ofString "withdrawal_rlp_len") := by
  refine ⟨_, _, _, lookup_withdrawal_rlp_len_fn, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_withdrawal_rlp_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_decCall hcode funLocFrame_rlp_word_encoded_len _ _ _
  intro t1 hc1
  apply M13.locFrame_decCall hc1 funLocFrame_rlp_word_encoded_len _ _ _
  intro t2 hc2
  apply M13.locFrame_decCall hc2 funLocFrame_rlp_word_encoded_len _ _ _
  intro t3 hc3
  apply M13.locFrame_dec
  intro _
  apply M13.locFrame_decCall (by exact hc3) funLocFrame_rlp_list_header_len _ _ _
  intro t4 _
  exact M13.locFrameW_eval _ rfl t4

/-! ### `LocFrame` of `block_rlp_length`'s entire tail after `heap_release(mark)` -/

def blockRlpTail : ProgHOL 64 :=
  match (sourceFunctionEntry Guest.Software.guestFn_block_rlp_length).2.2.1 with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ tail)) => tail
  | p => p

theorem locFrame_blockRlpTail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) :
    M13.LocFrame s (evaluateHOLFiniteState s blockRlpTail).2 := by
  dsimp only [blockRlpTail, sourceFunctionEntry, Guest.Software.guestFn_block_rlp_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_seq
  · refine M13.locFrame_while _ ?_ _ (by exact hcode)
    intro t htc
    apply M13.locFrame_dec; intro _
    apply M13.locFrame_dec; intro _
    apply M13.locFrame_seq
    · exact M13.locFrameW_eval _ rfl _
    · intro m1 hm1
      have hc1 : m1.code = originalRuntimeCode := hm1.code.trans htc
      apply M13.locFrame_dec; intro _
      apply M13.locFrame_seq
      · apply M13.locFrame_ite
        · exact M13.locFrame_call_local (by exact hc1) funLocFrame_rlp_bytes_encoded_len _
            (fun _ _ h => by cases h; rfl) _
        · exact M13.locFrameW_eval _ rfl _
      · intro m2 _
        exact M13.locFrameW_eval _ rfl m2
  · intro m3 hm3
    have hc3 : m3.code = originalRuntimeCode := hm3.code.trans (by exact hcode)
    apply M13.locFrame_decCall hc3 funLocFrame_rlp_list_header_len _ _ _
    intro t4 hc4
    apply M13.locFrame_seq
    · exact M13.locFrameW_eval _ rfl t4
    · intro m4 hm4
      have hc4' : m4.code = originalRuntimeCode := hm4.code.trans hc4
      apply M13.locFrame_seq
      · exact M13.locFrameW_eval _ rfl m4
      · intro m5 hm5
        have hc5 : m5.code = originalRuntimeCode := hm5.code.trans hc4'
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_seq
        · exact M13.locFrameW_eval _ rfl _
        · intro m6 hm6
          have hc6 : m6.code = originalRuntimeCode := hm6.code.trans (by exact hc5)
          apply M13.locFrame_seq
          · refine M13.locFrame_while _ ?_ m6 hc6
            intro tw htw
            apply M13.locFrame_decCall htw funLocFrame_withdrawal_rlp_len _ _ _
            intro tw2 _
            exact M13.locFrameW_eval _ rfl tw2
          · intro m7 hm7
            have hc7 := hm7.code.trans hc6
            apply M13.locFrame_seq
            · exact M13.locFrame_call_local hc7 funLocFrame_rlp_list_header_len _
                (fun _ _ h => by cases h; rfl) _
            · intro m8 hm8
              have hc8 := hm8.code.trans hc7
              apply M13.locFrame_seq
              · exact M13.locFrameW_eval _ rfl m8
              · intro m9 hm9
                have hc9 := hm9.code.trans hc8
                apply M13.locFrame_seq
                · exact M13.locFrame_call_local hc9 funLocFrame_rlp_list_header_len _
                    (fun _ _ h => by cases h; rfl) _
                · intro m10 _
                  exact M13.locFrameW_eval _ rfl m10

/-! ## 2. Exact post-state frames for `heap_mark`, `heap_release`, `alloc`, `rlp_encode_bytes`,
`rlp_encode_word`, `rlp_put_u256`, `rlp_encode_list_header`, and `encode_header` -/

/-- `ByteEffExceptHeap s post Rl`: like `M13.ByteRegionEffect`, except `heap_ptr` may change! -/
structure ByteEffHeap {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals_ne : ∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

theorem ByteEffHeap.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEffHeap s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ByteEffHeap.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : ByteEffHeap s post Rl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteEffHeap s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals_ne,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteEffHeap.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteEffHeap a b Rl) (h2 : ByteEffHeap b c Rl) :
    ByteEffHeap a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, fun k hk => (h2.globals_ne k hk).trans (h1.globals_ne k hk),
    ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx
    rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno
    rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

theorem ByteEffHeap.of_m11 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R1 R2 : List Ivl} (h : M11.ByteRegionEffect s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteEffHeap s post R2 ∧ post.globals = s.globals := by
  have hm := h.mono hsub
  exact ⟨⟨hm.code, hm.memaddrs, hm.shMemaddrs, hm.baseAddr, hm.be,
    fun _ _ => by rw [hm.globals], hm.out_dom, hm.cell_frame, hm.byte_frame⟩, hm.globals⟩

theorem ByteEffHeap.of_m13 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R1 R2 : List Ivl} (h : M13.ByteRegionEffect s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteEffHeap s post R2 ∧ post.globals = s.globals := by
  have hm := h.mono hsub
  exact ⟨⟨hm.code, hm.memaddrs, hm.shMemaddrs, hm.baseAddr, hm.be,
    fun _ _ => by rw [hm.globals], hm.out_dom, hm.cell_frame, hm.byte_frame⟩, hm.globals⟩

theorem ByteEffHeap.of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (Rl : List Ivl) (h : M13.LocFrame s post) :
    ByteEffHeap s post Rl ∧ post.globals = s.globals := by
  refine ⟨⟨h.code, by unfold M13.LocFrame at h; rw [h], by unfold M13.LocFrame at h; rw [h],
    by unfold M13.LocFrame at h; rw [h], h.be, fun _ _ => by rw [h.globals],
    fun _ _ => by rw [h.memory], fun _ _ => by rw [h.memory],
    fun _ _ _ => by unfold memB; rw [h.memory, h.be]⟩, h.globals⟩

theorem ByteEffHeap.to_m13_when_heap_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : ByteEffHeap s post Rl)
    (hhp : post.globals.lookup (ofString "heap_ptr") = s.globals.lookup (ofString "heap_ptr")) :
    M13.ByteRegionEffect s post Rl := by
  have hg : post.globals = s.globals := by
    apply HolFiniteMapExact.ext
    funext k
    by_cases hk : k = ofString "heap_ptr"
    · subst hk; exact hhp
    · exact h.globals_ne k hk
  exact ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, hg,
    h.out_dom, h.cell_frame, h.byte_frame⟩

theorem arenaReady_of_byteEffHeap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {q : BitVec 64}
    (hAs : ArenaReady s) (heff : ByteEffHeap s post Rl)
    (hq_lu : post.globals.lookup (ofString "heap_ptr") = some (.val (.word q)))
    (hq_lo : sourceBase ≤ q.toNat) (hq_hi : q.toNat ≤ heapLimit) (hq8 : q.toNat % 8 = 0) :
    ArenaReady post := by
  have hgP : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1
  have hhp : globN post "heap_ptr" = q.toNat := by simp [globN, hq_lu]
  have hfm : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [globN, heff.globals_ne (ofString "frame_mem_ptr") (by decide)]
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    simp [globN, heff.globals_ne (ofString "scratch_ptr") (by decide)]
  obtain ⟨_, _, h1, h2, h3, _, h4, h5, hgw⟩ := hAs.2
  have hgwP : GlobalsWord post := by
    refine globalsWord_frame ["heap_ptr"] (fun k hk => (heff.globals_ne k ?_).symm) ?_ hgw
    · simpa using hk
    · intro n _ hm
      have hneq : ofString n = ofString "heap_ptr" := by simpa using hm
      exact ⟨q, by unfold GlobalWord; rw [hneq]; exact hq_lu⟩
  refine ⟨hgP, ?_⟩
  unfold ArenaOK
  rw [hhp, hfm, hsc]
  exact ⟨hq_lo, hq_hi, h1, h2, h3, hq8, h4, h5, hgwP⟩

theorem worldOK_of_arenaReady_unhit_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hAp : ArenaReady post)
    (heff : ByteEffHeap s post [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
    (hhp_ge : globN s "heap_ptr" ≤ globN post "heap_ptr") :
    WorldOK post := by
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  have hag : AllocatorGrows s post := by
    refine ⟨hhp_ge, ?_⟩
    have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [globN, heff.globals_ne (ofString "scratch_ptr") (by decide)]
    rw [hsc]
  have hgs : WorldGlobalsSame s post := by
    refine ⟨fun gn hgn => ?_, fun g hg => ?_, ?_, ?_, ?_⟩
    · have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
      simp [globN, heff.globals_ne _ hne]
    · have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
      simp [globN, heff.globals_ne _ hne]
    · simp [globN, heff.globals_ne (ofString "journal") (by decide)]
    · simp [globN, heff.globals_ne (ofString "journal_cap") (by decide)]
    · simp [globN, heff.globals_ne (ofString "journal_n") (by decide)]
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, _, _, _, _⟩ := hAs.2
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hsb : 24 < sourceBase := by decide
    constructor
    · unfold memW
      rw [heff.cell_frame (BitVec.ofNat 64 8) (fun i hi hch => by
        simp only [List.mem_singleton] at hi; subst hi
        obtain ⟨h1, _⟩ := hch; dsimp at h1; omega)]
    · unfold memW
      rw [heff.cell_frame (BitVec.ofNat 64 16) (fun i hi hch => by
        simp only [List.mem_singleton] at hi; subst hi
        obtain ⟨h1, _⟩ := hch; dsimp at h1; omega)]
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i := by
    intro i hi a ha8 hhit
    apply heff.cell_frame a
    intro f hf hcf
    simp only [List.mem_singleton] at hf; subst hf
    rcases worldOwned_zero_or_allocated hWT i (worldTypedIvls_sub_worldOwned s S Nd i hi) with rfl | ⟨_, hal⟩
    · obtain ⟨_, h2⟩ := hhit; dsimp at h2; omega
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · obtain ⟨hc1, hc2⟩ := hcf; obtain ⟨hi1, hi2⟩ := hhit; dsimp at hc1 hc2; omega
      · obtain ⟨hc1, hc2⟩ := hcf; obtain ⟨hi1, hi2⟩ := hhit; dsimp at hc1 hc2
        have hsep : heapLimit ≤ scratchStart := by decide
        omega
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hres := worldTypedWith_congr_bo hAs hAp heff.be hag hgs hWT
    (fun t ht i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht, hi⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz]))
    (fun i hi _ => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun o ho => hunhit o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbo_g] using
        rec_word_eq_of_unhit hAs.2 hWT.2.2.1 "bo" 88 (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm_low
  exact ⟨hAp, S, (worldTyped_iff_with post S).2 ⟨Nd, hres.1⟩⟩

/-! ## 3. Callee step lemmas for `encode_header` and `block_rlp_length` -/

theorem eval_heap_mark_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_heap_mark)
    out.1 = some (.returned (.val (.word p))) ∧ M13.LocFrame s out.2 := by
  have hb : sourceFnBody Guest.Software.guestFn_heap_mark =
      .return (.var .global (ofString "heap_ptr")) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_return]
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp
  rw [hev]; dsimp only
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word p) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  exact ⟨rfl, (M13.LocFrame.refl s).emptyLocals⟩

theorem eval_heap_release_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (m p : BitVec 64) (Rl : List Ivl)
    (hm : s.locals.lookup (ofString "m") = some (.val (.word m)))
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_heap_release)
    out.1 = some (.returned (.val (.word 0))) ∧
    ByteEffHeap s out.2 Rl ∧
    out.2.globals.lookup (ofString "heap_ptr") = some (.val (.word m)) := by
  have hb : sourceFnBody Guest.Software.guestFn_heap_release =
      .seq
        (.assign .global (ofString "heap_ptr") (.var .local (ofString "m")))
        (.return (.const 0)) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  have hev_m : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "m")) = some (.val (.word m)) := hm
  rw [hev_m]; dsimp only
  have hv_ok : isValidValueHOLFinite s .global (ofString "heap_ptr") (.val (.word m)) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLExact, hp, shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hv_ok]; dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev0 : @evalHOLExact 64 F _ (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word m)) s).toExact
      (fun a => Classical.propDecidable ((setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word m)) s).memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hev0]; dsimp only
  have hsz : sizeOfShapeWithContextHOL
      (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word m)) s).structs
      (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
    intro k hk
    simp [emptyLocalsHOLFinite, setKvarHOLFinite, setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [emptyLocalsHOLFinite, setKvarHOLFinite, setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE]

theorem eval_alloc_body_byteEffHeap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn_lu : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)
    ∀ rv : ValueHOL 64, out.1 = some (.returned rv) →
      ∃ q : BitVec 64,
        rv = .val (.word p) ∧
        ArenaReady out.2 ∧
        ByteEffHeap s out.2 Rl ∧
        out.2.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧
        p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 := by
  dsimp only
  have hcMax_eq : InitECandidate.Solver.HeapPotential.cMax.toNat = heapLimit := rfl
  have hp_nat : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lu]
  have hp_le : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    have := hA.2.2.1; omega
  have hgen := M13.evaluate_alloc_body_general s p n hcode hp_le hp_lu hn_lu
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_alloc)
  have hinv := (M13.evaluateHOLFiniteState_guestInv_be s (sourceFnBody Guest.Software.guestFn_alloc) hA.1)
  intro rv hrv
  obtain ⟨hrv_eq, hg_eq, hm_eq, hpq, hq_le, hq8⟩ := hgen rv hrv
  set q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
  have hq_lu : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2.globals.lookup
      (ofString "heap_ptr") = some (.val (.word q)) := by
    rw [hg_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have heff : ByteEffHeap s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 Rl := by
    refine ⟨hmeta.1, hinv.1.memaddrs.trans hA.1.memaddrs.symm,
      hinv.1.shMemaddrs.trans hA.1.shMemaddrs.symm,
      hinv.1.baseAddr.trans hA.1.baseAddr.symm, hinv.2, ?_,
      fun _ _ => by rw [hm_eq], fun _ _ => by rw [hm_eq],
      fun _ _ _ => by unfold memB; rw [hm_eq, hinv.2]⟩
    intro k hk
    rw [hg_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  have hq_lo : sourceBase ≤ q.toNat := by
    have := hA.2.1; omega
  have hq_hi : q.toNat ≤ heapLimit := by omega
  have hAp : ArenaReady (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 :=
    arenaReady_of_byteEffHeap hA heff hq_lu hq_lo hq_hi hq8
  exact ⟨q, hrv_eq, hAp, heff, hq_lu, hpq, hq_hi, hq8⟩

/-- `ByteFrame Rl s t`: like `M13.ByteFrame`, except `t.globals` may update `"heap_ptr"`! -/
def ByteFrameHeap (Rl : List Ivl) {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t.code = s.code ∧
  t.memaddrs = s.memaddrs ∧
  t.shMemaddrs = s.shMemaddrs ∧
  t.baseAddr = s.baseAddr ∧
  t.be = s.be ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → t.globals.lookup k = s.globals.lookup k) ∧
  (∀ x : BitVec 64, t.memory x ≠ s.memory x → s.memaddrs x ∧ ∃ r ∈ Rl, CellHits x.toNat r) ∧
  (∀ a : Nat, a < 2 ^ 64 → memB t a ≠ memB s a → ∃ r ∈ Rl, InIvl a r)

theorem ByteFrameHeap.to_byteEffHeap {Rl : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrameHeap Rl s t) : ByteEffHeap s t Rl := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro a hna; by_contra hne; exact hna (h.2.2.2.2.2.2.1 a hne).1
  · intro a hno; by_contra hne; obtain ⟨_, ri, hri, hch⟩ := h.2.2.2.2.2.2.1 a hne; exact hno ri hri hch
  · intro b hb hno; by_contra hne; obtain ⟨ri, hri, hin⟩ := h.2.2.2.2.2.2.2 b hb hne; exact hno ri hri hin

theorem ByteFrameHeap.refl (Rl : List Ivl) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ByteFrameHeap Rl s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => False.elim (h rfl), fun _ _ h => False.elim (h rfl)⟩

theorem ByteFrameHeap.locals {Rl : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrameHeap Rl s t) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteFrameHeap Rl s { t with locals := L, clock := k } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem ByteFrameHeap.of_locFrame (Rl : List Ivl) {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : M13.LocFrame s t) : ByteFrameHeap Rl s t := by
  refine ⟨h.code, by unfold M13.LocFrame at h; rw [h], by unfold M13.LocFrame at h; rw [h],
    by unfold M13.LocFrame at h; rw [h], h.be, fun _ _ => by rw [h.globals],
    fun _ hne => False.elim (hne (by rw [h.memory])),
    fun _ _ hne => False.elim (hne (by unfold memB; rw [h.memory, h.be]))⟩

theorem ByteFrameHeap.of_byteEffHeap {Rl : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteEffHeap s t Rl) : ByteFrameHeap Rl s t := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals_ne, ?_, ?_⟩
  · intro x hne
    refine ⟨by by_contra hna; exact hne (h.out_dom x hna), ?_⟩
    by_contra hno
    exact hne (h.cell_frame x (fun r hr hch => hno ⟨r, hr, hch⟩))
  · intro a ha hne
    by_contra hno
    exact hne (h.byte_frame a ha (fun r hr hin => hno ⟨r, hr, hin⟩))

theorem ByteFrameHeap.trans {Rl : List Ivl} {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : ByteFrameHeap Rl s t) (h2 : ByteFrameHeap Rl t u) : ByteFrameHeap Rl s u :=
  ByteFrameHeap.of_byteEffHeap (h1.to_byteEffHeap.trans h2.to_byteEffHeap)

theorem ByteFrameHeap.mono {R1 R2 : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrameHeap R1 s t)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteFrameHeap R2 s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, ?_⟩
  · intro x hne
    obtain ⟨hdom, r, hr, hc1, hc2⟩ := h.2.2.2.2.2.2.1 x hne
    obtain ⟨j, hj, h1, h2⟩ := hsub r hr
    exact ⟨hdom, j, hj, by omega, by omega⟩
  · intro a ha hne
    obtain ⟨r, hr, ha1, ha2⟩ := h.2.2.2.2.2.2.2 a ha hne
    obtain ⟨j, hj, h1, h2⟩ := hsub r hr
    exact ⟨j, hj, by omega, by omega⟩

theorem byteFrameHeap_storeByte {Rl : List Ivl} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst src : ExpHOL 64)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      ∃ r ∈ Rl, InIvl addr.toNat r) :
    ByteFrameHeap Rl s (evaluateHOLFiniteState s (.storeByte dst src)).2 := by
  have hbf := M13.byteFrame_storeByte s dst src hin
  exact ⟨by rw [hbf.1], by rw [hbf.1], by rw [hbf.1], by rw [hbf.1], by rw [hbf.1],
    fun _ _ => by rw [hbf.1], hbf.2.1, hbf.2.2⟩

/-! ### `rlp_write_header`, `rlp_encode_list_header`, `rlp_encode_word`, `rlp_encode_bytes`, `rlp_put_u256` -/

theorem eval_rlp_write_header_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 base0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hbase : s.locals.lookup (ofString "base") = some (.val (.word base0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ h : BitVec 64, rv = .val (.word h) ∧ 1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_write_header =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
            (.return (.const 1)))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]))
            (.seq
              (.call (some (none, none)) (ofString "rlp_put_be")
                [.op .add [.var .local (ofString "dst"), .const 1],
                 .var .local (ofString "n"),
                 .var .local (ofString "ll")])
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt ⊢
  dsimp only at hnt ⊢
  have hsb_inv : ∀ (t : PanSemStateFiniteExact 64 F) (val : ExpHOL 64),
      t.memaddrs = ordinaryDomain →
      t.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
      (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none →
      dst0.toNat < heapEnd := by
    intro t val htma htdst hnone
    rw [evaluateHOLFiniteState_storeByte] at hnone
    simp only [evalHOLExact, htdst] at hnone
    split at hnone
    · split at hnone
      · rename_i m' hst
        unfold panMemStoreByteWord8HOL at hst; dsimp only at hst
        by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
        · exact (M11.byteAlign_lt_heapEnd htma dst0 hdom).2
        · simp [hdom] at hst
      · simp at hnone
    · simp at hnone
  have hsb_oe : ∀ (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64),
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∨
        (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
    intro t dst val
    rw [evaluateHOLFiniteState_storeByte]
    split <;> [split <;> [split <;> [exact Or.inl rfl; exact Or.inr rfl]; exact Or.inr rfl]; exact Or.inr rfl]
  by_cases hn55 : n0.toNat ≤ 55
  · rw [if_pos hn55] at hnt ⊢
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10] at hnt ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases hsb_oe s (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn
      dsimp only at hnt ⊢
      have hdst_lt_he := hsb_inv s _ hma hdst (by rw [hsb])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]; dsimp only
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨1, hrv''.symm, by decide, by decide, hdst_lt_he, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'
        exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
      injection hr with hr'; subst hr'
      rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  · rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    obtain ⟨ll, mid, hll8, hll_pos, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
      M11.eval_decCall_rlp_be_len s "ll" (.var .local (ofString "n")) n0 _ hcode
        (by simp [evalHOLExact, hn]) hnt
    have hll1 : 1 ≤ ll.toNat := hll_pos (by
      intro h0; subst h0; simp at hn55)
    rw [hr_eq, hs_eq]
    have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
    have hmid_ma : mid.memaddrs = ordinaryDomain := by rw [hmid_eq]; exact hma
    have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      have hne : ofString "ll" ≠ ofString "n" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hn]
    have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have hne : ofString "ll" ≠ ofString "dst" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hdst]
    have heff_s_mid : M11.ByteRegionEffect s mid Rl := by
      rw [hmid_eq]; exact M11.ByteRegionEffect.refl s Rl |>.with_locals_clock mid.locals mid.clock
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
    rcases hsb : evaluateHOLFiniteState mid
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
    simp only [hsb] at hnt_m ⊢
    rcases hsb_oe mid (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn
      dsimp only at hnt_m ⊢
      have hdst_lt_he := hsb_inv mid _ hmid_ma hmid_dst (by rw [hsb])
      obtain ⟨heff_hdr, hs2_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
      have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
      have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hs2_loc]; exact hmid_dst
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        rw [hs2_loc]; exact hmid_n
      have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hs2_loc]; exact hmid_ll
      have hhe_val : heapEnd = 33806089704 := by decide
      have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
        rw [BitVec.toNat_add]
        change (dst0.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by omega
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
      rcases hc_put : evaluateHOLFiniteState s2
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .var .local (ofString "n"),
           .var .local (ofString "ll")]) with ⟨rc, s3⟩
      have hnt_put : rc ≠ some .timeOut := by
        rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
      have hput := M11.eval_call_rlp_put_be s2
        (.op .add [.var .local (ofString "dst"), .const 1])
        (.var .local (ofString "n"))
        (.var .local (ofString "ll"))
        (dst0 + 1) n0 ll Rl hs2_code
        (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hs2_n])
        (by simp [evalHOLExact, hs2_ll])
        hfit
        (fun _ => by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
        (by rw [hc_put]; exact hnt_put)
      dsimp only at hput
      rw [hc_put] at hput
      simp only [hc_put] at hnt_m ⊢
      cases rc with
      | some r =>
        dsimp only
        have hnr := hput.2 (by simp)
        refine ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)), fun r' hr' _ => ?_⟩
        injection hr' with hr''; subst hr''
        rintro (⟨v, hv⟩ | ⟨e, v, hv, he⟩)
        · exact hnr (Or.inl ⟨v, hv⟩)
        · exact hnr (Or.inr ⟨e, v, hv, he⟩)
      | none =>
        dsimp only at hnt_m ⊢
        obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
        have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs3_loc]; exact hs2_ll
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ s3.toExact
            (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .add [.const 1, .var .local (ofString "ll")]) =
            some (.val (.word (1 + ll))) := by
          simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]; dsimp only
        have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz]; dsimp only
        have h1ll_nat : (1 + ll).toNat = 1 + ll.toNat := by
          rw [BitVec.toNat_add]
          change (1 + ll.toNat) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
        · injection hrv with hrv'; injection hrv' with hrv''
          exact ⟨1 + ll, hrv''.symm, by omega, by omega, hdst_lt_he,
            (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
        · injection hr with hr'; subst hr'
          exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
      injection hr with hr'; subst hr'
      rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem eval_rlp_header_len_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)
    ∀ rv : ValueHOL 64, out.1 = some (.returned rv) →
      ∃ h : BitVec 64, rv = .val (.word h) ∧ 1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧ M13.LocFrame s out.2 := by
  have hlf : M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2 := by
    obtain ⟨p, b, rs, hl, hf⟩ := funLocFrame_rlp_header_len
    have hb_eq : b = sourceFnBody Guest.Software.guestFn_rlp_header_len := by
      rw [lookup_rlp_header_len_fn] at hl
      injection hl with hl'; exact (Prod.mk.inj (Prod.mk.inj hl').2).1.symm
    subst hb_eq; exact hf s hcode
  have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.return (.const 1))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  dsimp only
  intro rv hrv
  have hrv' := hrv
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hrv'
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt hrv'
  dsimp only at hnt hrv'
  by_cases hn55 : n0.toNat ≤ 55
  · rw [if_pos hn55] at hrv'
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10, evaluateHOLFiniteState_return] at hrv'
    have hev1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.const 1) = some (.val (.word 1)) := rfl
    rw [hev1] at hrv'; dsimp only at hrv'
    have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hsz] at hrv'; dsimp only at hrv'
    injection hrv' with h1; injection h1 with h2
    exact ⟨1, h2.symm, by decide, by decide, hlf⟩
  · rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hrv'
    dsimp only at hnt hrv'
    obtain ⟨ll, mid, hll8, _, hmid_loc, _, _, hr_eq, _⟩ :=
      M11.eval_decCall_rlp_be_len s "ll" (.var .local (ofString "n")) n0 _ hcode
        (by simp [evalHOLExact, hn]) hnt
    rw [hr_eq, evaluateHOLFiniteState_return] at hrv'
    have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hev_ret : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.const 1, .var .local (ofString "ll")]) = some (.val (.word (1 + ll))) := by
      simp [evalHOLExact, evalListHOLExact, hmid_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hev_ret] at hrv'; dsimp only at hrv'
    have hsz : sizeOfShapeWithContextHOL mid.structs (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hsz] at hrv'
    injection hrv' with h1; injection h1 with h2
    have h1ll : (1 + ll).toNat = 1 + ll.toNat := by
      rw [BitVec.toNat_add]
      change (1 + ll.toNat) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨1 + ll, h2.symm, by omega, by omega, hlf⟩

theorem eval_rlp_list_header_len_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "payload_len") = some (.val (.word n0)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)
    ∀ rv : ValueHOL 64, out.1 = some (.returned rv) →
      ∃ h : BitVec 64, rv = .val (.word h) ∧ 1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧ M13.LocFrame s out.2 := by
  have hlf : M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).2 := by
    obtain ⟨p, b, rs, hl, hf⟩ := funLocFrame_rlp_list_header_len
    have hb_eq : b = sourceFnBody Guest.Software.guestFn_rlp_list_header_len := by
      rw [lookup_rlp_list_header_len_fn] at hl
      injection hl with hl'; exact (Prod.mk.inj (Prod.mk.inj hl').2).1.symm
    subst hb_eq; exact hf s hcode
  have hb : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
  dsimp only
  intro rv hrv
  have hrv' := hrv
  rw [hb, evaluateHOLFiniteState_call] at hnt hrv'
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "payload_len")] = some [.val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_header_len) n0
    (by rw [hcode]; exact lookup_rlp_header_len_fn)
  rw [hargs] at hnt hrv'; dsimp only at hnt hrv'
  rw [hlook] at hnt hrv'; dsimp only at hnt hrv'
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt hrv'
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word n0)))
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl; rw [hrun] at hnt; exact hnt rfl
    have hstep := eval_rlp_header_len_body_step entry n0 hcode hent_n (by rw [hrun]; exact hnt_b)
    rw [hrun] at hstep hrv'
    cases br with
    | none => simp at hrv'
    | some r =>
      cases r with
      | returned v =>
        dsimp only at hrv'
        split at hrv'
        · injection hrv' with hrv''; injection hrv'' with hrv'''
          subst hrv'''
          obtain ⟨h, rfl, hh1, hh9, _⟩ := hstep v rfl
          exact ⟨h, rfl, hh1, hh9, hlf⟩
        · simp at hrv'
      | _ => simp at hrv'

theorem eval_rlp_encode_list_header_call_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : evalAt s dstExp = some (.val (.word dst0)))
    (hn : evalAt s nExp = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, nExp])).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, nExp])
    out.1 = none → ByteEffHeap s out.2 Rl ∧ out.2.globals = s.globals ∧ out.2.locals = s.locals := by
  dsimp only
  intro hnone
  rw [evaluateHOLFiniteState_call] at hnt hnone ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, nExp] = some [.val (.word dst0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalAt] at hdst hn ⊢
    simp [hdst, hn]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 n0
    (by decide) (by rw [hcode]; exact lookup_rlp_encode_list_header_fn)
  rw [hargs] at hnt hnone ⊢; dsimp only at hnt hnone ⊢
  rw [hlook] at hnt hnone ⊢; dsimp only at hnt hnone ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt hnone ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_len", ValueHOL.val (.word n0))
    set entry := callEntryStateHOLFinite s cmap
    have hb_eq : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
        .call none (ofString "rlp_write_header")
          [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have hne : ofString "payload_len" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hent_pl : entry.locals.lookup (ofString "payload_len") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hin_args : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] =
        some [.val (.word dst0), .val (.word 192), .val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_pl]
    have hin_look := pan_three_word_lookup entry.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 192 n0
      (by decide) (by decide) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact M11.lookup_rlp_write_header)
    rcases hout1 : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) with ⟨r1, st1⟩
    simp only [hout1] at hnone ⊢
    have hnt1 : r1 ≠ some .timeOut := by
      rintro rfl; rw [hout1] at hnt; exact hnt rfl
    have hout1' := hout1
    rw [hb_eq, evaluateHOLFiniteState_call, hin_args] at hout1'
    dsimp only at hout1'
    rw [hin_look] at hout1'
    dsimp only at hout1'
    by_cases hclk1 : entry.clock = 0
    · rw [if_pos hclk1] at hout1'; injection hout1' with hr _; exact absurd hr.symm hnt1
    · rw [if_neg hclk1] at hout1'
      set cmap2 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 192))).update (ofString "n", ValueHOL.val (.word n0))
      set entry2 := callEntryStateHOLFinite entry cmap2
      have he2_dst : entry2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        have h1 : ofString "n" ≠ ofString "dst" := by decide
        have h2 : ofString "base" ≠ ofString "dst" := by decide
        simp [entry2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      have he2_base : entry2.locals.lookup (ofString "base") = some (.val (.word 192)) := by
        have h1 : ofString "n" ≠ ofString "base" := by decide
        simp [entry2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1]
      have he2_n : entry2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [entry2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hout2 : evaluateHOLFiniteState entry2 (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨r2, st2⟩
      rw [hout2] at hout1'
      have hnt2 : r2 ≠ some .timeOut := by
        rintro rfl; simp at hout1'; exact hnt1 hout1'.1.symm
      obtain ⟨hret2, _⟩ := eval_rlp_write_header_body_step entry2 dst0 192 n0 Rl
        hcode hma he2_dst he2_base he2_n hin_ivl (by rw [hout2]; exact hnt2)
      rw [hout2] at hret2
      cases r2 with
      | none => simp at hout1'; rcases hout1' with ⟨rfl, rfl⟩; simp at hnone
      | some r2' =>
        cases r2' with
        | returned rv2 =>
          dsimp only at hout1'
          split at hout1'
          · injection hout1' with hr1 hst1
            subst hr1 hst1
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh_outer
              rw [if_pos hsh_outer]
              obtain ⟨_, _, _, _, _, heff2⟩ := hret2 rv2 rfl
              have heff_s_e2 : M11.ByteRegionEffect s entry2 Rl :=
                M11.ByteRegionEffect.refl s Rl |>.with_locals_clock entry2.locals entry2.clock
              have heff_all := (heff_s_e2.trans heff2).with_locals_clock s.locals st2.clock
              obtain ⟨heff_h, hg_eq⟩ := ByteEffHeap.of_m11 heff_all (fun i hi => ⟨i, hi, le_rfl, le_rfl⟩)
              exact ⟨heff_h, hg_eq, rfl⟩
            · contradiction
          · injection hout1' with hr1 _; subst hr1; simp at hnone
        | «break» => simp at hout1'; rcases hout1' with ⟨rfl, _⟩; simp at hnone
        | «continue» => simp at hout1'; rcases hout1' with ⟨rfl, _⟩; simp at hnone
        | exception _ _ => simp at hout1'; rcases hout1' with ⟨rfl, _⟩; simp at hnone
        | timeOut => exact absurd rfl hnt2
        | error => simp at hout1'; rcases hout1' with ⟨rfl, _⟩; simp at hnone
        | finalFfi _ => simp at hout1'; rcases hout1' with ⟨rfl, _⟩; simp at hnone

end InitECandidate.Solver.Wave8GuestInv.R13Shards

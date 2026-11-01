/- Tail-handler facts extracted from PanToStackAllocIdentityAndUnconditionalNoGcCall.lean (SHA256 30852a0a172a0a888f5b071dce297eda676cd0eed59200e7b7d42fd25dd40f73). -/
import InitECandidate.Solver.Wave8Stage.Static.PanToStackRawCallNoAllocAndStackAllocStructural
set_option autoImplicit false
namespace InitECandidate.Solver.Wave8Stage.Static.PanToStackAllocIdentityAndUnconditionalNoGcCall

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.Wave8Stage.Static.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.Wave8Stage.Static.PanToStackRawCallNoAllocAndStackAllocStructural (NoTailHandler NoGcCall)

variable {width : Nat} [NeZero width]

/-! ## WordToStack and StackRawCall never put a handler on a tail call -/

theorem h_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    NoTailHandler (wStackLoadNative l x) = NoTailHandler x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, NoTailHandler, Bool.true_and]; exact h_stackLoad ps x

theorem h_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, NoTailHandler (g n) = true) : NoTailHandler (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [NoTailHandler, hg]

theorem h_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    NoTailHandler (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [h_stackLoad]) <;>
    first | rfl | (apply h_regWrite1; intro n; rfl)

theorem h_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    NoTailHandler (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, NoTailHandler, Bool.and_eq_true]
      refine ⟨?_, h_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem h_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    NoTailHandler (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact h_wMoveAux _ _

theorem h_seqStackFree (n : Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    NoTailHandler (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [NoTailHandler] using h

theorem h_copyRetAux (k f : Nat) : ∀ n, NoTailHandler (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, NoTailHandler, Bool.true_and]
      exact h_copyRetAux k f n

theorem h_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : NoTailHandler kont = true) :
    NoTailHandler (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [NoTailHandler, Bool.and_eq_true]
    exact ⟨h_copyRetAux _ _ _, h_seqStackFree _ _ h⟩

theorem h_stackMove (start offset i : Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    ∀ n, NoTailHandler (stackMoveNative n start offset i p) = true := by
  intro n
  induction n generalizing start with
  | zero => exact h
  | succ n ih =>
      rw [stackMoveNative]; simp only [NoTailHandler, Bool.and_true]; exact ih _

theorem h_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    NoTailHandler (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact h_stackMove _ _ _ _ rfl _

theorem h_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    NoTailHandler (callDestNative (width := width) pos args kf).1 = true := by
  unfold callDestNative; split
  · rfl
  · split
    · rfl
    · dsimp only; rw [h_stackLoad]; rfl

theorem h_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    NoTailHandler (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

theorem h_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : NoTailHandler p = true) : NoTailHandler (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [NoTailHandler] using h

theorem h_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : NoTailHandler (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem h_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    NoTailHandler (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [h_stackLoad]) <;> first | rfl | (apply h_regWrite1; intro n; rfl)

/-- WordToStack never creates a StackLang `storeConsts` from a `NoSt` WordLang body. -/
theorem h_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), NoSt p = true → NoTailHandler (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [compNative]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨h_compNative conf perf a _ _ h.1, h_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := h_compNative conf perf a bs kf h.1
      have hb := h_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [h_stackLoad]; simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [h_stackLoad]; simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [NoTailHandler, Bool.true_and]; rw [h_stackLoad]
          simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact h_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact h_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨h_callDest _ _ _, h_seqStackFree _ _ rfl⟩
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      simp only [NoSt, Bool.and_true] at h
      have hr := h_compNative conf perf rc (wLiveNative live bs kf).2 kf h
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true, Bool.and_true]
      refine ⟨h_callDest _ _ _, h_wLive _ _ _, h_stackArgs _ _ _, ?_, ?_⟩
      · split <;> rfl
      · refine ⟨?_, h_copyRet _ _ _ _ _ hr⟩
        split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc, h1, h2)), bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have hr := h_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1
      have hh := h_compNative conf perf hc
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true]
      refine ⟨h_callDest _ _ _, h_wLive _ _ _, h_pushHandler _ _ _ _,
        h_stackArgs _ _ _, ?_, ⟨?_, h_copyRet _ _ _ _ _ (h_popHandler _ _ _ hr)⟩, hh⟩
      · split <;> rfl
      · split <;> rfl
  | .storeConsts .., _, _, h => by simp [NoSt] at h
  | .move .., bs, kf, h => by rw [compNative]; exact h_wMove _ _
  | .inst i, bs, kf, h => by rw [compNative]; exact h_wInst _ _
  | .return v vs, bs, kf, h => by
      rw [compNative]; dsimp only; rw [h_stackLoad]; exact h_seqStackFree _ _ rfl
  | .opCurrHeap .., bs, kf, h => by
      rw [compNative]; dsimp only; rw [h_stackLoad]; apply h_regWrite1; intro; rfl
  | .set name e, bs, kf, h => by
      rw [compNative.eq_def]; dsimp only
      repeat' split
      all_goals first | rfl | (rw [h_stackLoad]; rfl)
  | .get d st, bs, kf, h => by
      rw [compNative]; exact h_regWrite1 (fun r => .get r (storeNameOfWord st)) d kf (fun _ => rfl)
  | .locValue d l, bs, kf, h => by
      rw [compNative]; exact h_regWrite1 (fun n => .locValue n l 0) d kf (fun _ => rfl)
  | .alloc _ live, bs, kf, h => by
      rw [compNative]; simp only [NoTailHandler, Bool.and_true]; exact h_wLive _ _ _
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [h_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact h_wShareInst _ _ _ _
  | .skip, _, _, _ | .raise .., _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem h_compileProgNative (conf : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width)) (ac rc : Nat) (bs : AppList (BitVec width) × Nat)
    (h : NoSt p = true) : NoTailHandler (compileProgNative conf perf p ac rc bs).1 = true := by
  unfold compileProgNative; dsimp only
  simp only [NoTailHandler, Bool.true_and]; exact h_compNative conf perf p _ _ h

theorem h_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, NoSt x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, NoTailHandler y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h_compileProgNative conf perf p ac rc bs (h _ (List.mem_cons_self ..))
      · exact h_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every *compiled body* is `NoTailHandler`; the only
StackLang `storeConsts` is the fixed prepended stub. -/
theorem h_compileNative_bodies (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ NoTailHandler y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact h_compileWordToStack conf perf _ progs _ h y hy

theorem th_compSeq (a b fb : HolProg width) (info : Spt Nat) (hfb : NoTailHandler fb = true) :
    NoTailHandler (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq; split
  · exact hfb
  · split
    · exact hfb
    · split
      · rfl
      · split <;> rfl

theorem th_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, NoTailHandler p = true → NoTailHandler (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; apply th_compSeq
      simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact th_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [NoTailHandler, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_true]
      exact th_rawCallComp info p1 h
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info p1 h.1, th_rawCallComp info p2 h.2⟩
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .shMemOp .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h
  | .stackAlloc .., h | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h
  | .stackLoadAny .., h | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem th_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    NoTailHandler (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [NoTailHandler, Bool.and_eq_true] at h
    simp only [NoTailHandler, Bool.and_eq_true]
    exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  · exact th_rawCallComp info p h



end InitECandidate.Solver.Wave8Stage.Static.PanToStackAllocIdentityAndUnconditionalNoGcCall

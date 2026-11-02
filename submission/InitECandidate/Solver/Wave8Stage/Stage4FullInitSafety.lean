import InitECandidate.Solver.Wave8Stage.Stage4HeapSafety
import InitECandidate.Solver.Wave8Stage.Stage4

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
variable {width : Nat} [NeZero width]

theorem mapSafe_updateList {K : Type} [DecidableEq K] {bad : Nat}
    (m : HolFiniteMapExact K (WordLocW width)) (entries : List (K × WordLocW width))
    (hm : MapSafe bad m) (he : ∀ e ∈ entries, ValueSafe bad e.2) :
    MapSafe bad (m.updateListEq entries) := by
  induction entries generalizing m with
  | nil => exact hm
  | cons e es ih =>
    have hh : m.updateListEq (e :: es) = (m.updateEq e).updateListEq es := by
      apply HolFiniteMapExact.ext_lookup
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_LIST_HOL_cons]
      rfl
    rw [hh]
    exact ih _ (mapSafe_update hm e.1 e.2 (he e (by simp)))
      (fun e' h => he e' (List.mem_cons_of_mem _ h))

theorem mapSafe_mapKeys {A B : Type} {bad : Nat} (f : A → B)
    (hf : Function.Injective f) (m : HolFiniteMapExact A (WordLocW width))
    (hm : MapSafe bad m) : MapSafe bad (HolFiniteMapExact.mapKeys f m) := by
  intro k v hv
  have hd : (HolFiniteMapExact.mapKeys f m).lookup k ≠ none := by rw [hv]; simp
  obtain ⟨a, _, ha⟩ := ((HolFiniteMapExact.mapKeys_spec f m).1 k).mp hd
  rw [ha, HolFiniteMapExact.lookup_mapKeys_of_injective hf] at hv
  exact hm a v hv

theorem coreSafe_labMakeInit {C F : Type} {bad : Nat}
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (regs : List Nat) (saveRegs : Nat → Bool) (s : LabSem.State width C F)
    (hr : ∀ r ∈ regs, ValueSafe bad (s.regs r))
    (hm : MemorySafe bad s.memDomain s.memory) :
    CoreSafe bad (StackToLab.Proofs.MakeInit.makeInit code oracle regs saveRegs s) := by
  constructor
  · apply mapSafe_updateList _ _ (mapSafe_empty bad)
    intro e he
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp he
    exact hr r hr'
  · exact hm

theorem coreSafe_namesMakeInit {C F : Type} {bad : Nat}
    (f : Spt Nat) (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F)
    (hf : Function.Bijective (StackNames.findNameSpt f)) (hs : CoreSafe bad s) :
    CoreSafe bad (StackNames.makeInit f code oracle s) := by
  refine ⟨mapSafe_mapKeys _ ?_ _ hs.regs, hs.memory⟩
  intro a b hab
  have hinv := apply_holLinv_of_surjective hf.2
  have hh := congrArg (StackNames.findNameSpt f) hab
  simpa only [hinv] using hh

/-- The standard fullMakeInit assumptions supply all initial register facts.
The separate memory premise is exactly the runtime label exclusion needed. -/
theorem fullMakeInit_s2_coreSafe {C F : Type} {bad : Nat}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (hm : MemorySafe bad t.memDomain t.memory) :
    CoreSafe bad
      (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle) := by
  obtain ⟨_, _, _, _, hmem, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩ := hA
  obtain ⟨p2, p3, p4, bp, h2, h3, h4, _⟩ := hmem
  apply coreSafe_namesMakeInit _ _ _ _ hf
  apply coreSafe_labMakeInit _ _ _ _ _ _ hm
  intro r hr
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h2]; trivial
  · rw [h3]; trivial
  · rw [h4]; trivial

/-- Runtime safety of the real reduced state, with initialization and its
separation relation discharged by FullMakeInit's existing assumptions. -/
theorem fullMakeInit_reduced_stateSafe {C F : Type} {bad : Nat}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (hb : 1 ≠ bad) (hm : MemorySafe bad t.memDomain t.memory) :
    StateSafe bad
      (StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
        bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
        (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
        (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)) := by
  have hcore := fullMakeInit_s2_coreSafe sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle hA hm
  obtain ⟨post, w2, w3, w4, run, _, _, _, _, _, _, _, _, _, rel, _⟩ :=
    Pancake.Proofs.PanToTarget.panToTargetInitCodeRun hA
  have hp := coreSafe_initCode hb (StackToLab.isGenGc dc.gcKind) maxHeap sp _ hcore
  rw [run] at hp
  have hs := stateSafe_of_remove_relation sc.jump offset sp _ post rel hp hp.regs
  obtain ⟨s1, hopt, _⟩ := StackRemove.Proofs.InitSemantics.makeInitSemantics sc.jump
    offset (StackToLab.isGenGc dc.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle)
    (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code)
    (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
    bitmaps dataSp
    ⟨StackToLab.Proofs.FullMakeInitSemantics.dischargeThese_s2 hA,
      StackToLab.Proofs.FullMakeInitSemantics.propagateThese_s2 hA⟩
  unfold StackRemove.Proofs.InitMake.makeInitAny
  rw [hopt]
  unfold StackRemove.Proofs.InitMake.makeInitOpt at hopt
  rw [run] at hopt
  simp only at hopt
  split at hopt
  · cases hopt
    exact hs
  · cases hopt

/-- The concrete machine initialization contract excludes location values at
all aligned addresses, hence on every aligned Lab memory domain. -/
theorem memorySafe_of_goodInitState {S Q : Type} (bad : Nat)
    (mc : MachineConfig width S Q) (ms : S) (bytes : List (BitVec 8))
    (cbspace : Nat) (t : AsmState width) (m : BitVec width → WordLocW width)
    (dm sdm domain : BitVec width → Bool)
    (hgi : goodInitState mc ms bytes cbspace t m dm sdm)
    (halign : ∀ a, domain a = true → holByteAligned a = true) :
    MemorySafe bad domain m := by
  intro a ha
  obtain ⟨w, hw⟩ := goodInitState_wordMemory hgi a
  have hh := halign a ha
  change decide (holByteAlign a = a) = true at hh
  have hh := of_decide_eq_true hh
  rw [hh] at hw
  rw [hw]
  trivial

/-- At the actual initialized StackRemove input, deleting stub 6 preserves
entry results. Both compiled-code safety and runtime-state safety are derived. -/
theorem fullMakeInit_entry_without_stub {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (conf : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (wc : WordToWord.Config)
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (source : List (Pancake.PanLang.DeclHOL width))
    (hcode : code = (WordToStack.Native.compileNative conf perf
      (WordToWord.compile wc conf (panToWordCompileProgHOL arch source)).2).2.2.2)
    (hm : MemorySafe storeConstsStubLocation t.memDomain t.memory)
    (ho : ∀ i, (oracle i).2.1 = []) (start k : Nat) (hn : start ≠ storeConstsStubLocation) :
    let initial := StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
      bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
      (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
      (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
    (StackSemEvaluate.evaluate (.call none (.inl start) none,
      { initial with clock := k, code := sptFromAList (withoutSection storeConstsStubLocation
        (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code)) })).1 =
      (StackSemEvaluate.evaluate (.call none (.inl start) none, { initial with clock := k })).1 := by
  intro initial
  have hs := fullMakeInit_reduced_stateSafe sc dc maxHeap sp offset bitmaps code t saveRegs
    dataSp oracle hA (by decide : 1 ≠ storeConstsStubLocation) hm
  have he : initial.code = sptFromAList (StackAlloc.compile dc (StackRawCall.compile code)) :=
    StackRemove.Proofs.InitAny.makeInitAnyCode ..
  have hor : ∀ i, (initial.compileOracle i).2.1 = [] := by
    intro i
    change ((StackRemove.Proofs.InitMake.makeInitAny _ _ _ _ _ _ _ _ _ _).compileOracle i).2.1 = []
    rw [StackRemove.Proofs.InitAny.makeInitAnyCompileOracle]
    simp [StackToLab.Proofs.FullMakeInitSemantics.coracle1, ho]
  have he' := he
  rw [hcode] at he'
  have hh := pancake_entry_without_stub dc conf perf wc arch source
    { initial with clock := k } start he' (hs.withClock k) hn hor
  simpa only [StackToLab.Proofs.FullMakeInitSemantics.code1, hcode] using hh



end InitECandidate.Solver.Wave8Stage.RuntimeLabels

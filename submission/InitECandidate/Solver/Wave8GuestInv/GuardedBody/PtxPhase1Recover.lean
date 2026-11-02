import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Transitions
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def recoverArgs : List (ExpHOL 64) := [.var .local (ofString "tx"),
  .load .one (.op .add [.var .global (ofString "be"), .const 0]), .var .local (ofString "sender")]

theorem hoare_recover_sender (h : PtxCallees) :
    Hoare SenderAllocated (.call (some (none,none)) (ofString "recover_sender_with_chain_id") recoverArgs)
      (fun r t => r = none → StageP 1 t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨v1,v2,v3,he1,he2,he3,hp,hq,hr⟩ := params_three_values s
    (ofString "recover_sender_with_chain_id") (ofString "tx") (ofString "chain_id") (ofString "out20")
    .one .one .one _ .one (by rw [hc]; exact lookup_recover_sender_with_chain_id)
    (.var .local (ofString "tx"))
    (.load .one (.op .add [.var .global (ofString "be"), .const 0])) (.var .local (ofString "sender"))
    vs body callee ret ha hl
  have hout : locN (callEntryStateHOLFinite s callee) "out20" = locN s "sender" := by
    simp only [locN, callEntryStateHOLFinite, hr, show s.locals.lookup (ofString "sender") = some v3 from he3]
  have hspec := funSpec_at_lookup h.wk_recover_sender_with_chain_id s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hspec
  have hstep := hspec (Or.inl ⟨v,rfl⟩)
  have hs := worldStep_with_locals hstep s.locals s.clock
  change WorldStep (fun _ => [(locN (callEntryStateHOLFinite s callee) "out20",20),
    (globN s "keccak_pad",136),(globN s "keccak_st",200),(globN s "u256_ws",640)]) _ _ _ s _ post at hs
  rw [hout] at hs
  obtain ⟨S,Nd,hW,hT,hTyped,hTx,hRecs⟩ := hP.2.2
  have hA := hP.1.1.1.1
  have hin : Inside (locN s "sender",20) (locN s "sender") (locN s "sender" + 24) := ⟨le_rfl,by omega⟩
  have hRT : IvlsDisj [(locN s "sender",20),(globN s "keccak_pad",136),
      (globN s "keccak_st",200),(globN s "u256_ws",640)] (worldTypedIvls s S Nd) := by
    intro i hi j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact disj_of_inside_left hin (hTyped j hj)
    · exact buffer_disj_typed hA.2 hW (gn := ("keccak_pad",136)) (by decide) (by decide) (by decide) (by decide) j hj
    · exact buffer_disj_typed hA.2 hW (gn := ("keccak_st",200)) (by decide) (by decide) (by decide) (by decide) j hj
    · exact buffer_disj_typed hA.2 hW (gn := ("u256_ws",640)) (by decide) (by decide) (by decide) (by decide) j hj
  have hR0 : ∀ i ∈ [(locN s "sender",20),(globN s "keccak_pad",136),
      (globN s "keccak_st",200),(globN s "u256_ws",640)], i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp
  have hReady : TxReadyStrong {post with locals := s.locals} := by
    apply txReadyStrong_worldStep hs hA (txEnv_of_ready hP.1) hP.1.2.1 hW hT
      (by decide) (by decide) (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide)
      (fun i hi => hRT i hi _ (bo_mem_typed hP.1.1.2.1)) hR0 hRT
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact disj_of_inside_right hin hTx
      · exact input_disj_buffer hT.2.1.1 hT.2.2.1 (gn := ("keccak_pad",136)) (by decide) (by decide) (by decide)
      · exact input_disj_buffer hT.2.1.1 hT.2.2.1 (gn := ("keccak_st",200)) (by decide) (by decide) (by decide)
      · exact input_disj_buffer hT.2.1.1 hT.2.2.1 (gn := ("u256_ws",640)) (by decide) (by decide) (by decide)
    · intro ht hn i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      have hRe := (hT.2.2.2 ht).2.1 hn
      rcases hi with rfl | rfl | rfl | rfl
      · exact disj_of_inside_right hin (hRecs ht hn)
      · exact input_disj_buffer hRe.2.1.1 hRe.2.2 (gn := ("keccak_pad",136)) (by decide) (by decide) (by decide)
      · exact input_disj_buffer hRe.2.1.1 hRe.2.2 (gn := ("keccak_st",200)) (by decide) (by decide) (by decide)
      · exact input_disj_buffer hRe.2.1.1 hRe.2.2 (gn := ("u256_ws",640)) (by decide) (by decide) (by decide)
  have hSender := senderOK_grows hA.1 hReady.1.1.1.1 hs.2.1 rfl hP.2.1
  exact ⟨hReady,fun _ => hSender,by omega,by omega,by omega⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1

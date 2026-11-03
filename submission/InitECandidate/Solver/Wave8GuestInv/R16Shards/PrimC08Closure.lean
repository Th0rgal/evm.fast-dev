import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard08
import InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard09a
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256
import InitECandidate.Solver.Wave8GuestInv.R13Shards.NodeRlpKeep
import InitECandidate.Solver.Wave8GuestInv.R13Shards.MptNibbleKey
import InitECandidate.Solver.Wave8GuestInv.R13Shards.HtabSetSpec
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewExt
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfInsertIntoLeaf
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfSplitExtension
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeRlp
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeHash
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptRoot
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfCollapseBranch
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfDeleteExtFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptNibbleKeyWW
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptInsertFinal
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabUnionIntoSpec
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ProcessWithdrawals
import InitECandidate.Solver.Wave8GuestInv.R16Shards.IncorporateTxIntoBlock
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkMarkAccountCreated
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkGetCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

/-! Direct standalone aggregator (`PrimC08Closure`) wiring verified 0-sorry `C00`, `C08`, and
`C09..C21` theorems into `PrimitivesProved.lean` while keeping `ContractParts/C00..C21` frozen. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `C00` Contract Closure (`htab_*`, `mpt_*`, `frame_exception_spec`, `mem_init_world`) -/

theorem htab_new_spec : type_of% @InitECandidate.Solver.Wave8GuestInv.htab_new_spec :=
  InitECandidate.Solver.Wave8GuestInv.htab_new_spec

theorem htab_set_spec : type_of% @InitECandidate.Solver.Wave8GuestInv.htab_set_spec :=
  InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet.htab_set_spec_proof

theorem htab_union_into_spec : type_of% @InitECandidate.Solver.Wave8GuestInv.htab_union_into_spec :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.htab_union_into_spec

theorem mpt_insert_node_spec : type_of% @InitECandidate.Solver.Wave8GuestInv.mpt_insert_node_spec :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.mpt_insert_node_spec_proof

theorem frame_exception_spec : type_of% @InitECandidate.Solver.Wave8GuestInv.frame_exception_spec :=
  InitECandidate.Solver.Wave8GuestInv.frame_exception_spec

theorem mem_init_world : type_of% @InitECandidate.Solver.Wave8GuestInv.mem_init_world :=
  InitECandidate.Solver.Wave8GuestInv.mem_init_world

/-! ## 2. `C08` Callee Contract Closure (`ww_*`, `sp_*`, `nf_*`, `rt_*`, `ak_*`, `nk_*`, `wk_*`) -/

theorem «ww__resolve_step» :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep.«ww__resolve_step»

theorem «sp__resolve_step» :
    ResolvesNode (ofString "_resolve_step") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep.«sp__resolve_step»

theorem «ww_mpt_nibble_key» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
      ["heap_ptr"] (ofString "mpt_nibble_key") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.ww_mpt_nibble_key

theorem «nk_mpt_nibble_key» :
    RetNibbles (ofString "mpt_nibble_key") :=
  InitECandidate.Solver.Wave8GuestInv.R13MptKeepsTwin.nk_mpt_nibble_key_proof

theorem «ak__node_rlp_begin» :
    KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_begin") :=
  InitECandidate.Solver.Wave8GuestInv.R13NodeRlpKeep.ak__node_rlp_begin

theorem «ak__node_rlp_finish» :
    KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_finish") :=
  InitECandidate.Solver.Wave8GuestInv.R13NodeRlpKeep.ak__node_rlp_finish

theorem «nf__collapse_branch» :
    NodeFn ["node"] (fun s Nd => NodeKind s Nd "node" 3) (ofString "_collapse_branch") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«nf__collapse_branch»

theorem «nf__delete_ext_finish» :
    NodeFn ["node", "nc"]
      (fun s Nd => NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))
      (ofString "_delete_ext_finish") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«nf__delete_ext_finish»

theorem «nf__insert_into_leaf» :
    NodeFn ["node"]
      (fun s Nd => NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧ locN s "vlen" < 2 ^ 40)
      (ofString "_insert_into_leaf") :=
  InitECandidate.Solver.Wave8GuestInv.R14Shards.«nf__insert_into_leaf»

theorem «nf__split_extension» :
    NodeFn ["node"]
      (fun s Nd => NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
        locN s "vlen" < 2 ^ 40 ∧ locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")
      (ofString "_split_extension") :=
  InitECandidate.Solver.Wave8GuestInv.R14Shards.«nf__split_extension»

theorem «nf_node_new_ext» :
    NodeFn ["child"] (fun s Nd => KeyIn s Nd (locN s "nib") (locN s "nlen")) (ofString "node_new_ext") :=
  InitECandidate.Solver.Wave8GuestInv.R14Shards.«nf_node_new_ext»

theorem «rt_node_new_ext» :
    Returns ArenaReady (fun s post p => FreshBlock s post p 56) (ofString "node_new_ext") :=
  InitECandidate.Solver.Wave8GuestInv.R14Shards.«rt_node_new_ext»

theorem «nf_node_new_leaf» :
    NodeFn [] (fun s Nd => KeyIn s Nd (locN s "nib") (locN s "nlen") ∧ locN s "vlen" < 2 ^ 40)
      (ofString "node_new_leaf") :=
  InitECandidate.Solver.Wave8GuestInv.R14Shards.«nf_node_new_leaf»

theorem «wk_alloc» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«wk_alloc»

theorem «rt_alloc» :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«rt_alloc»

theorem «wk_mpt_new» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«wk_mpt_new»

theorem «rt_mpt_new» :
    Returns ArenaReady
      (fun s post m => FreshBlock s post m 16 ∧ memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«rt_mpt_new»

theorem «wk_htab_copy» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧ ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
        (fun _ post w => htabFootprint post w))
      (ofString "htab_copy") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«wk_htab_copy»

theorem «rt_htab_copy» :
    Returns ArenaReady
      (fun s post n => locN s "t" ≠ 0 ∧
        (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
          HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧
          ∀ i ∈ htabFootprint post n, Inside i (globN s "heap_ptr") (globN post "heap_ptr")))
      (ofString "htab_copy") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01.«rt_htab_copy»

theorem «wk_msg_new» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Wk06b.«wk_msg_new»

theorem «wk_te_new» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Wk06b.«wk_te_new»

theorem «wk_lst_new» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
        (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")]))
      (ofString "lst_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Wk06b.«wk_lst_new»

theorem «wk_keccak256» :
    WorldKeeps WorldOK
      (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "keccak256") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.wk_keccak256_impl

theorem «wk_record_pre_state_read» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "record_pre_state_read") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_record_pre_state_read»

theorem «wk_mark_account_created» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "mark_account_created") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_mark_account_created»

theorem «wk_get_code» :
    WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "get_code") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_get_code»

theorem «wk_track_ancestor_access» :
    WorldKeeps WorldOK (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "track_ancestor_access") :=
  InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard08.«wk_track_ancestor_access»

theorem «wk_block_rlp_length» :
    WorldKeeps ((fun s => WorldOK s ∧ HeaderOK s)) (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "block_rlp_length") :=
  InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard09a.«wk_block_rlp_length»

/-! ## 3. `C09..C21` Guarded Body (`gbody_*`) Closure -/

theorem «gbody__decode_witness_node_body» : GBody.«_decode_witness_node_body» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody__decode_witness_node_body»

theorem «gbody__mpt_delete_node_body» : GBody.«_mpt_delete_node_body» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody__mpt_delete_node_body»

theorem «gbody__mpt_insert_node» : GBody.«_mpt_insert_node» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody__mpt_insert_node»

theorem «gbody_node_rlp» : GBody.«node_rlp» :=
  InitECandidate.Solver.Wave8GuestInv.P3C10C12.«gbody_node_rlp»

theorem «gbody_node_hash» : GBody.«node_hash» :=
  InitECandidate.Solver.Wave8GuestInv.P3C10C12.«gbody_node_hash»

theorem «gbody_mpt_root» : GBody.«mpt_root» :=
  InitECandidate.Solver.Wave8GuestInv.P3C10C12.«gbody_mpt_root»

theorem «gbody_mpt_set» : GBody.«mpt_set» :=
  InitECandidate.Solver.Wave8GuestInv.P3C10C12.«gbody_mpt_set»

theorem «gbody_idx_start_storage» : GBody.«idx_start_storage» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_idx_start_storage»

theorem «gbody_update_builder_from_tx» : GBody.«update_builder_from_tx» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_update_builder_from_tx»

theorem «gbody_incorporate_tx_into_block» : GBody.«incorporate_tx_into_block» :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«gbody_incorporate_tx_into_block»

theorem «gbody_htab_truncate» : GBody.«htab_truncate» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_htab_truncate»

theorem «gbody_rollback_child_access» : GBody.«rollback_child_access» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_rollback_child_access»

theorem «gbody_finish_child» : GBody.«finish_child» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_finish_child»

theorem «gbody_get_storage» : GBody.«get_storage» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_get_storage»

theorem «gbody_op_sload» : GBody.«op_sload» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_op_sload»

theorem «gbody_op_sstore» : GBody.«op_sstore» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_op_sstore»

theorem «gbody_process_message» : GBody.«process_message» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_process_message»

theorem «gbody_process_create_message» : GBody.«process_create_message» :=
  InitECandidate.Solver.Wave8GuestInv.«gbody_process_create_message»

theorem «gbody_process_message_call» : GBody.«process_message_call» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21.«gbody_process_message_call»

theorem «gbody_process_general_purpose_requests» : GBody.«process_general_purpose_requests» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21.«gbody_process_general_purpose_requests»

theorem «gbody_process_withdrawals» : GBody.«process_withdrawals» :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«gbody_process_withdrawals»

theorem «gbody_state_init» : GBody.«state_init» :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.gbody_state_init

theorem «gbody_main» : GBody.«main» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21.«gbody_main»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure

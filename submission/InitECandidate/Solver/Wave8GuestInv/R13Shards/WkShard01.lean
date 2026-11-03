import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01HtabCopy
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop

/-! Shard `WkShard01`: `C08` contracts for `alloc`, `mpt_new`, `htab_copy`, and `cache_get_root`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem «wk_alloc» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.wk_alloc_impl

theorem «rt_alloc» :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
    (ofString "alloc") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.rt_alloc_impl

theorem «rt_mpt_new» :
    Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
    (ofString "mpt_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.rt_mpt_new_impl

theorem «wk_mpt_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.wk_mpt_new_impl

theorem «rt_htab_copy» :
    Returns ArenaReady (fun s post n => locN s "t" ≠ 0 ∧
      (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
        HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧
        ∀ i ∈ htabFootprint post n, Inside i (globN s "heap_ptr") (globN post "heap_ptr")))
    (ofString "htab_copy") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.rt_htab_copy_impl

theorem «wk_htab_copy» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧
        ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
      (fun _ post w => htabFootprint post w)) (ofString "htab_copy") :=
  InitECandidate.Solver.Wave8GuestInv.R13Shards.wk_htab_copy_impl

theorem «wk_cache_get_root» :
    WorldKeeps WorldOK
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
               (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
               (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "cache_get_root") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_cache_get_root»

theorem «wk_ws_get_account_optional» :
    WorldKeeps WorldOK
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
               (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
               (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "ws_get_account_optional") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_ws_get_account_optional»

theorem «wk_ws_storage_root_of» :
    WorldKeeps WorldOK
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
               (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
               (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "ws_storage_root_of") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.«wk_ws_storage_root_of»

end InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01

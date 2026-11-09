import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.MptSetRootKeeps

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open private mpt_set_params_unpack_sc mpt_set_body_eff_strong
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.MptSetRootKeeps

abbrev mptSetB_sc : List (String × Nat) :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_hash_scratch", 40)]

abbrev mptSetR_sc {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]

theorem mk_mpt_set_eff_strong :
    FunSpec MptSetReadyStrong
      (fun s r post => Resumes r →
        MptEffStrong mptSetR_sc mptSetB_sc ["heap_ptr", "scratch_ptr"] s post)
      (ofString "mpt_set") := by
  refine ⟨[(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one),
           (ofString "vptr", .one), (ofString "vlen", .one)],
          sourceFnBody Guest.Software.guestFn_mpt_set,
          .one, P3MptSet.lookup_mpt_set, ?_⟩
  intro F state hcode hP hshape _ hres
  obtain ⟨wm, wkey, wklen, wvptr, wvlen, hlk_m, hlk_key, hlk_klen, hlk_vptr, hlk_vlen⟩ :=
    mpt_set_params_unpack_sc state P3MptSet.lookup_mpt_set hshape
  exact mpt_set_body_eff_strong state wm wkey wklen wvptr wvlen hcode hP
    hlk_m hlk_key hlk_klen hlk_vptr hlk_vlen hres

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

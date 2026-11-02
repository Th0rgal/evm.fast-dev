import InitECandidate.Proofs.BitmapImageFacts

namespace InitECandidate.Solver.BitmapInstallationCompact
open InitE Flapjack
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def rom (bytes : List (BitVec 8)) (a : BitVec 64) : BitVec 8 :=
  if initialPc ≤ a.toNat ∧ a.toNat < initialPc + bytes.length then
    bytes[a.toNat - initialPc]?.getD 0 else 0


def memory (bytes : List (BitVec 8)) (a : BitVec 64) : BitVec 8 :=
  if sourceBase ≤ a.toNat ∧ a.toNat < sourceBase + 40 then
    wordByte (Guest.startupHeaders[(a.toNat - sourceBase) / 8]?.getD 0)
      ((a.toNat - sourceBase) % 8)
  else if initDataRam ≤ a.toNat ∧ a.toNat < initDataRam + 24 then
    wordByte ([BitVec.ofNat 64 sourceBase, BitVec.ofNat 64 stackStart,
      BitVec.ofNat 64 ramEnd][(a.toNat - initDataRam) / 8]?.getD 0)
      ((a.toNat - initDataRam) % 8)
  else if initDataRam + 24 ≤ a.toNat ∧ a.toNat < initDataEnd then
    rom bytes (BitVec.ofNat 64 (initDataRom + a.toNat - initDataRam))
  else rom bytes a


private theorem slice_byte {α : Type} (bytes : List α) (fallback : α)
    (start count offset : Nat) (hi : offset < count) :
    (((bytes.drop start).take count)[offset]?).getD fallback =
      (bytes[start + offset]?).getD fallback := by
  simp only [List.getElem?_take, hi, if_true, List.getElem?_drop]


private theorem mapped_byte (words : List (BitVec 64)) (offset : Nat)
    (hi : offset < 8 * words.length) :
    (((List.range (8 * words.length)).map fun i =>
      wordByte (words[i / 8]?.getD 0) (i % 8))[offset]?).getD 0 =
      wordByte (words[offset / 8]?.getD 0) (offset % 8) := by
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]


private theorem image_byte (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (himage : (bytes.drop (initDataRom-initialPc+24)).take (8*words.length) =
      (List.range (8*words.length)).map fun offset =>
        wordByte (words[offset/8]?.getD 0) (offset%8))
    (offset : Fin (8*words.length)) :
    bytes[initDataRom-initialPc+24+offset.val]?.getD 0 =
      wordByte (words[offset.val/8]?.getD 0) (offset.val%8) := by
  have h := congrArg (fun values : List (BitVec 8) => values[offset.val]?.getD 0) himage
  rw [slice_byte _ _ _ _ _ offset.isLt] at h
  exact h.trans (mapped_byte words offset.val offset.isLt)


private theorem wordByte_getByte (word : BitVec 64) (offset : Nat) (ho : offset < 8) :
    wordByte word offset = HolByte.getByte (BitVec.ofNat 64 offset) word false := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordByte, HolByte.getByte, HolByte.byteIndex, Bool.false_eq_true, ↓reduceIte,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : offset < 2^64),Nat.mod_eq_of_lt ho]


private theorem copied_byte (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (hsize : bytes.length = 1028080) (hlen : words.length = 4603)
    (himage : (bytes.drop (initDataRom-initialPc+24)).take (8*words.length) =
      (List.range (8*words.length)).map fun offset =>
        wordByte (words[offset/8]?.getD 0) (offset%8))
    (i : Fin words.length) (j : Fin 8) :
    memory bytes (BitVec.ofNat 64 (initDataRam+24+8*i.val) + BitVec.ofNat 64 j.val) =
      HolByte.getByte (BitVec.ofNat 64 j.val) (words[i.val]'i.isLt) false := by
  have hi : i.val < 4603 := by simpa only [hlen] using i.isLt
  have hj := j.isLt
  have hbound : 8*i.val+j.val < 8*words.length := by
    have hil := i.isLt
    omega
  have hdiv : (8*i.val+j.val)/8 = i.val := by omega
  have hmod : (8*i.val+j.val)%8 = j.val := by omega
  have ha : (BitVec.ofNat 64 (initDataRam+24+8*i.val) + BitVec.ofNat 64 j.val).toNat =
      initDataRam+24+8*i.val+j.val := by
    rw [BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [initDataRam]; omega)]
  have hs : ¬ (sourceBase ≤ initDataRam+24+8*i.val+j.val ∧
      initDataRam+24+8*i.val+j.val < sourceBase+40) := by
    simp only [sourceBase,initDataRam]; omega
  have hd : ¬ (initDataRam ≤ initDataRam+24+8*i.val+j.val ∧
      initDataRam+24+8*i.val+j.val < initDataRam+24) := by omega
  have hb : initDataRam+24 ≤ initDataRam+24+8*i.val+j.val ∧
      initDataRam+24+8*i.val+j.val < initDataEnd := by
    simp only [initDataRam,initDataEnd]; omega
  rewrite [memory,ha,if_neg hs,if_neg hd,if_pos hb]
  have hrom : initDataRom+(initDataRam+24+8*i.val+j.val)-initDataRam = initDataRom+24+8*i.val+j.val := by omega
  rewrite [hrom]
  unfold rom
  have hrt : (BitVec.ofNat 64 (initDataRom+24+8*i.val+j.val)).toNat = initDataRom+24+8*i.val+j.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by simp only [initDataRom]; omega)]
  rewrite [hrt,if_pos (by simp only [initialPc,initDataRom,hsize]; omega)]
  have hoff : initDataRom+24+8*i.val+j.val-initialPc = initDataRom-initialPc+24+(8*i.val+j.val) := by
    simp only [initDataRom,initialPc]; omega
  rewrite [hoff,image_byte bytes words himage ⟨8*i.val+j.val,hbound⟩]
  rewrite [hdiv,hmod,List.getElem?_eq_getElem i.isLt]
  exact wordByte_getByte _ _ j.isLt



/-- The concrete ROM is supplied only after the generic copied-byte argument
has been kernel checked, avoiding reductions through the megabyte image. -/
theorem installed_bitmap_byte (i : Fin InitECandidate.bitmaps.length) (j : Fin 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*i.val) + BitVec.ofNat 64 j.val) =
      HolByte.getByte (BitVec.ofNat 64 j.val) (InitECandidate.bitmaps[i.val]'i.isLt) false :=
  copied_byte InitECandidate.code InitECandidate.bitmaps submitted_image_size bitmap_count
    bitmap_image_bytes i j


theorem installed_bitmap_word (i : Fin InitECandidate.bitmaps.length) :
    packedMemoryWord installedMemory (BitVec.ofNat 64 (initDataRam+24+8*i.val)) =
      (InitECandidate.bitmaps[i.val]'i.isLt) := by
  apply packedMemoryWord_of_bytes
  · unfold holByteAligned
    rw [holLOG2_eq_log2 (by decide)]
    change holAligned 3 (BitVec.ofNat 64 (initDataRam+24+8*i.val)) = true
    apply (holAligned_iff _ _).mpr
    change (BitVec.ofNat 64 (initDataRam+24+8*i.val)).toNat % 8 = 0
    have hi : i.val < 4603 := by simpa only [bitmap_count] using i.isLt
    simp only [BitVec.toNat_ofNat]
    have hbase : initDataRam+24+8*i.val < 2^64 := by
      simp only [initDataRam]; omega
    rw [Nat.mod_eq_of_lt hbase]
    simp [initDataRam,Nat.add_mod,Nat.mul_mod_right]
  · exact installed_bitmap_byte i

end InitECandidate.Solver.BitmapInstallationCompact

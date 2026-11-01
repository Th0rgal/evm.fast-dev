#!/usr/bin/env python3
"""Kernel-check BitmapInstallation without eagerly unfolding the ROM literals.

The fixed source is copied to the cache, with local irreducibility attributes for
the million-byte code list and bitmap list. List indexing and memory reading are
factored through generic lemmas so simplification never traverses the literal ROM. All
original theorem statements are unchanged. The attributes are scoped to a section
and do not escape into the resulting module. No fixed repository source is edited.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
MODULE = Path('InitECandidate/Proofs/BitmapInstallation')

GENERIC_BYTE = '''
private theorem bitmap_image_byte_generic
    (code : List (BitVec 8)) (bitmaps : List (BitVec 64)) (base : Nat)
    (image : (code.drop base).take (8 * bitmaps.length) =
      (List.range (8 * bitmaps.length)).map (fun offset =>
        wordByte (bitmaps[offset / 8]?.getD 0) (offset % 8)))
    (offset : Fin (8 * bitmaps.length)) :
    code[base + offset.val]?.getD 0 =
      wordByte (bitmaps[offset.val / 8]?.getD 0) (offset.val % 8) := by
  have h := congrArg (fun bytes : List (BitVec 8) => bytes[offset.val]?.getD 0) image
  simpa [List.getElem?_take, offset.isLt, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range, Nat.add_comm] using h

'''


# Adapted from ArtifactInstallation/{ROMRead,CopyByte,ROMByte,InstalledByte}.lean
# on integration commit 7d5ef0bc5c40b5ebcc146985511b45a6fec0738b.
MEMORY_HELPERS = '''
private theorem read_rom_byte (bytes : List (BitVec 8)) (pc address : Nat)
    (lower : pc ≤ address) (upper : address < pc + bytes.length)
    (limit : address < 2^64) :
    (if pc ≤ (BitVec.ofNat 64 address).toNat ∧
        (BitVec.ofNat 64 address).toNat < pc + bytes.length then
      bytes[(BitVec.ofNat 64 address).toNat - pc]?.getD 0 else 0) =
      bytes[address-pc]?.getD 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt limit, if_pos ⟨lower,upper⟩]


private theorem initial_memory_byte (address : Nat)
    (lower : initialPc ≤ address) (upper : address < initialPc + 1028080)
    (limit : address < 2^64) :
    initialMemory (BitVec.ofNat 64 address) =
      InitECandidate.code[address-initialPc]?.getD 0 := by
  exact read_rom_byte InitECandidate.code initialPc address lower
    (by rw [InitECandidate.Proofs.LiteralFacts.code_length]; exact upper) limit


private theorem installed_memory_bitmap_copy (index byte : Nat)
    (hi : index < 4603) (hj : byte < 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte) =
      initialMemory (BitVec.ofNat 64 (initDataRom+24+8*index+byte)) := by
  have ha : (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte).toNat =
      initDataRam+24+8*index+byte := by
    rw [BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [initDataRam]; omega)]
  have hs : ¬ (sourceBase ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < sourceBase+40) := by
    simp only [sourceBase,initDataRam]; omega
  have hd : ¬ (initDataRam ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < initDataRam+24) := by omega
  have hb : initDataRam+24 ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < initDataEnd := by
    simp only [initDataRam,initDataEnd]; omega
  rw [installedMemory,ha,if_neg hs,if_neg hd,if_pos hb]
  have hrom : initDataRom+(initDataRam+24+8*index+byte)-initDataRam = initDataRom+24+8*index+byte := by omega
  rw [hrom]


private theorem installed_memory_bitmap_rom_byte (index byte : Nat)
    (hi : index < 4603) (hj : byte < 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte) =
      InitECandidate.code[initDataRom-initialPc+24+(8*index+byte)]?.getD 0 := by
  rw [installed_memory_bitmap_copy index byte hi hj]
  rw [initial_memory_byte (initDataRom+24+8*index+byte)
    (by simp only [initialPc,initDataRom]; omega)
    (by simp only [initialPc,initDataRom]; omega)
    (by simp only [initDataRom]; omega)]
  have hoff : initDataRom+24+8*index+byte-initialPc =
      initDataRom-initialPc+24+(8*index+byte) := by
    simp only [initDataRom,initialPc]; omega
  rw [hoff]

'''

INSTALLED_BYTE_PROOF = '''  have hi : i.val < 4603 := by simpa only [bitmap_count] using i.isLt
  have hj := j.isLt
  have bound : 8*i.val+j.val < 8*InitECandidate.bitmaps.length := by
    have small := i.isLt
    omega
  have hdiv : (8*i.val+j.val)/8 = i.val := by omega
  have hmod : (8*i.val+j.val)%8 = j.val := by omega
  calc
    _ = InitECandidate.code[initDataRom-initialPc+24+(8*i.val+j.val)]?.getD 0 :=
      installed_memory_bitmap_rom_byte i.val j.val hi j.isLt
    _ = wordByte (InitECandidate.bitmaps[(8*i.val+j.val)/8]?.getD 0)
        ((8*i.val+j.val)%8) := bitmap_image_byte ⟨_,bound⟩
    _ = wordByte InitECandidate.bitmaps[i] j.val := by
      rw [hdiv,hmod,List.getElem?_eq_getElem i.isLt]
      rfl
    _ = _ := wordByte_getByte _ _ j.isLt
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--max-memory', type=int, default=24576)
    args = parser.parse_args()
    args.cache = args.cache.resolve()
    original = ROOT / 'submission' / MODULE.with_suffix('.lean')
    raw = original.read_text()
    opening = 'namespace InitE\nopen Flapjack\n'
    closing = 'end InitE\n'
    assert raw.count(opening) == raw.count(closing) == 1
    scoped_opening = (opening + '\nsection\n'
                      'attribute [local irreducible] InitECandidate.code InitECandidate.bitmaps\n')
    scoped_closing = 'end\n\n' + closing
    source = raw.replace(opening, scoped_opening).replace(closing, scoped_closing)
    assert source.replace(scoped_opening, opening).replace(scoped_closing, closing) == raw
    proof_start = source.index('  have h := congrArg')
    proof_end = source.index('\nprivate theorem wordByte_getByte', proof_start)
    original_proof = source[proof_start:proof_end]
    generic_application = '''  exact bitmap_image_byte_generic InitECandidate.code InitECandidate.bitmaps
    (initDataRom-initialPc+24) bitmap_image_bytes offset
'''
    source = source[:proof_start] + generic_application + source[proof_end:]
    source = source.replace('private theorem bitmap_image_byte (',
                            GENERIC_BYTE + 'private theorem bitmap_image_byte (', 1)
    assert (source.replace(GENERIC_BYTE, '').replace(generic_application, original_proof)
            .replace(scoped_opening, opening).replace(scoped_closing, closing)) == raw
    byte_start = source.index('  have hi :', source.index('theorem installed_bitmap_byte'))
    byte_end = source.index('\ntheorem installed_bitmap_word', byte_start)
    original_byte_proof = source[byte_start:byte_end]
    source = source[:byte_start] + INSTALLED_BYTE_PROOF + '\n' + source[byte_end:]
    source = source.replace('private theorem bitmap_image_byte_generic',
                            MEMORY_HELPERS + '\nprivate theorem bitmap_image_byte_generic', 1)
    restored = source.replace(MEMORY_HELPERS + '\n', '', 1)
    restored = restored.replace(INSTALLED_BYTE_PROOF + '\n', original_byte_proof, 1)
    assert (restored.replace(GENERIC_BYTE, '').replace(generic_application, original_proof)
            .replace(scoped_opening, opening).replace(scoped_closing, closing)) == raw

    def progress(label):
        return f'run_elab do\n  dbg_trace "{label}"\n\n'

    source = source.replace('section\nattribute', progress('checking attributes') + 'section\nattribute', 1)
    source = re.sub(r'(?m)^(private )?theorem (\w+)',
                    lambda m: progress('checking ' + m[2]) + m[0], source)
    source += '\n#print axioms InitE.installed_bitmap_byte\n#print axioms InitE.installed_bitmap_word\n'
    source_root = args.cache / 'bitmap-prebuild/source'
    generated = source_root / MODULE.with_suffix('.lean')
    generated.parent.mkdir(parents=True, exist_ok=True)
    generated.write_text(source)
    output = ROOT / '.lake/build/lib/lean' / MODULE.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = args.cache / 'logs/BitmapInstallation.log'
    log.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    if not environment.get('LEAN_PATH'):
        paths = sorted((ROOT / '.lake/packages').glob('*/.lake/build/lib/lean'))
        environment['LEAN_PATH'] = os.pathsep.join(map(str, [*paths, ROOT / '.lake/build/lib/lean']))
    command = ['lean', '-j1', f'-M{args.max_memory}', '-DElab.async=false', '-Dprofiler=true',
               '-R', str(source_root), '-o', str(output), str(generated)]
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT)
    diagnostic = log.read_text()
    axioms = {name: [a.strip() for a in names.split(',') if a.strip()]
              for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
                                            diagnostic)}
    if result.returncode == 0:
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for name in ('InitE.installed_bitmap_byte', 'InitE.installed_bitmap_word'):
            assert name in axioms and set(axioms[name]) <= allowed, (name, axioms)
        assert output.is_file()
    evidence = {'original_source_sha256': hashlib.sha256(raw.encode()).hexdigest(),
                'elaboration_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
                'elaboration_changes': ['section-local irreducibility of code and bitmaps',
                                        'factor bitmap_image_byte through a generic list lemma',
                                        'factor installed_bitmap_byte through generic ROM-reading lemmas'],
                'command': command, 'exit': result.returncode, 'axioms': axioms,
                'seconds': round(time.monotonic() - start, 2)}
    if result.returncode == 0:
        evidence['olean_sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
    (args.cache / 'logs/bitmap-prebuild.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(diagnostic[-12000:])
    print('BitmapInstallation exit:', result.returncode, flush=True)
    raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()

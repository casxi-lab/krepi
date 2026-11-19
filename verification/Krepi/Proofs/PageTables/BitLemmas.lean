module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the bits of descriptors

Lemmas about the descriptors of the specification of the `page-tables`
component, for every proof that reads an entry of a pool:

- bitwise identities of `UInt64`: `u64_or_and` (`&&&` distributes over
  `|||`);
- the zero entry: `isValid_zero`, `isPlain_zero`;
- the attributes of a kind: `attr_and_not_mask`;
- table descriptors: `isPlain_tableDescriptor`, `typeBits_tableDescriptor`,
  `isValid_tableDescriptor`, `outputAddress_tableDescriptor`;
- page descriptors: `typeBits_descriptor`, `isValid_descriptor`,
  `outputAddress_descriptor`, `descriptor_outputAddress` and
  `isPlain_descriptor` (a page descriptor is no table descriptor), with
  `ofPage_isSome_iff` (what `Kind.ofPage` finds);
- block descriptors: `typeBits_blockDescriptor`,
  `blockAddress_blockDescriptor`, `isReadWriteBlock_blockDescriptor`, and
  what a block or a table descriptor is from its check
  (`typeBits_of_isReadWriteBlock`, `typeBits_of_isPlain`,
  `isValid_of_isPlain`, `isPlain_of_isReadWriteBlock`);
- output addresses: `outputAddress_le`, `blockAddress_le`,
  `blockAddress_mod`, `outputAddress_of_aligned` (an aligned address below
  $2^{48}$ is its own output address) and `direct_or` (`DIRECT_BASE | a` is a
  sum below $2^{39}$).

The other lemmas of the module are private steps of these.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

theorem u64_or_and (x y m : UInt64) : (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt64.toBitVec_inj.1; simp [BitVec.and_or_distrib_right]

private theorem u64_and_or_self (x m : UInt64) : (x &&& m) ||| m = m := by
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.getElem_and, BitVec.getElem_or]
  cases m.toBitVec[i] <;> simp

private theorem typeBits_or3 (x : UInt64) : typeBits (x ||| TABLE_OR_PAGE) = TABLE_OR_PAGE := by
  simp only [typeBits, u64_or_and]
  rw [show TABLE_OR_PAGE &&& 3 = 3 by decide]; exact u64_and_or_self _ _

theorem isValid_zero : isValid 0 = false := by decide
theorem isPlain_zero : isPlainTableDescriptor 0 = false := by decide

private theorem attr_and_mask (k : Kind) : k.attributes.bits &&& ADDRESS_MASK = 0 := by cases k <;> decide
theorem attr_and_not_mask (k : Kind) : k.attributes.bits &&& ~~~ADDRESS_MASK = k.attributes.bits := by
  cases k <;> decide
private theorem attr_or3_ne (k : Kind) : (k.attributes.bits ||| TABLE_OR_PAGE) ≠ TABLE_OR_PAGE := by
  cases k <;> decide

theorem isPlain_tableDescriptor (a : UInt64) : isPlainTableDescriptor (tableDescriptor a) = true := by
  simp only [isPlainTableDescriptor, tableDescriptor, u64_or_and, UInt64.and_assoc]
  rw [show ADDRESS_MASK &&& ~~~ADDRESS_MASK = 0 by decide]
  simp only [UInt64.and_zero, UInt64.zero_or]; decide

theorem typeBits_tableDescriptor (a : UInt64) : typeBits (tableDescriptor a) = TABLE_OR_PAGE :=
  typeBits_or3 _

theorem isValid_tableDescriptor (a : UInt64) : isValid (tableDescriptor a) = true := by
  simp [isValid, typeBits_tableDescriptor, TABLE_OR_PAGE]

theorem outputAddress_tableDescriptor (a : UInt64) :
    outputAddress (tableDescriptor a) = outputAddress a := by
  simp only [outputAddress, tableDescriptor, u64_or_and, UInt64.and_assoc, UInt64.and_self]
  rw [show TABLE_OR_PAGE &&& ADDRESS_MASK = 0 by decide, UInt64.or_zero]

theorem typeBits_descriptor (k : Kind) (a : UInt64) : typeBits (descriptor k a) = TABLE_OR_PAGE :=
  typeBits_or3 _

theorem isValid_descriptor (k : Kind) (a : UInt64) : isValid (descriptor k a) = true := by
  simp [isValid, typeBits_descriptor, TABLE_OR_PAGE]

theorem outputAddress_descriptor (k : Kind) (a : UInt64) :
    outputAddress (descriptor k a) = outputAddress a := by
  simp only [outputAddress, descriptor, u64_or_and, UInt64.and_assoc, UInt64.and_self, attr_and_mask]
  rw [show TABLE_OR_PAGE &&& ADDRESS_MASK = 0 by decide, UInt64.or_zero, UInt64.or_zero]

theorem descriptor_outputAddress (k : Kind) (a : UInt64) :
    descriptor k (outputAddress a) = descriptor k a := by
  simp only [descriptor, outputAddress, UInt64.and_assoc, UInt64.and_self]

theorem isPlain_descriptor (k : Kind) (a : UInt64) : isPlainTableDescriptor (descriptor k a) = false := by
  simp only [isPlainTableDescriptor, descriptor, u64_or_and, UInt64.and_assoc, attr_and_not_mask]
  rw [show ADDRESS_MASK &&& ~~~ADDRESS_MASK = 0 by decide,
    show TABLE_OR_PAGE &&& ~~~ADDRESS_MASK = TABLE_OR_PAGE by decide, UInt64.and_zero, UInt64.zero_or]
  simpa using attr_or3_ne k

private theorem blockDescriptor_eq (p : UInt64) : blockDescriptor p =
    (p &&& BLOCK_ADDRESS_MASK) ||| (Kind.readWrite.attributes.bits ||| 1) := by
  simp only [blockDescriptor, descriptor, u64_or_and, UInt64.and_assoc, UInt64.or_assoc]
  rw [show BLOCK_ADDRESS_MASK &&& (ADDRESS_MASK &&& ~~~2) = BLOCK_ADDRESS_MASK by decide,
    show Kind.readWrite.attributes.bits &&& ~~~2 = Kind.readWrite.attributes.bits by decide,
    show TABLE_OR_PAGE &&& ~~~2 = 1 by decide]

theorem typeBits_blockDescriptor (p : UInt64) : typeBits (blockDescriptor p) = BLOCK := by
  rw [blockDescriptor_eq]
  simp only [typeBits, u64_or_and, UInt64.and_assoc]
  rw [show BLOCK_ADDRESS_MASK &&& 3 = 0 by decide,
    show Kind.readWrite.attributes.bits &&& 3 = 0 by decide, show (1 : UInt64) &&& 3 = 1 by decide]
  simp [BLOCK]

theorem blockAddress_blockDescriptor (p : UInt64) :
    blockAddress (blockDescriptor p) = blockAddress p := by
  rw [blockDescriptor_eq]
  simp only [blockAddress, u64_or_and, UInt64.and_assoc, UInt64.and_self]
  rw [show Kind.readWrite.attributes.bits &&& BLOCK_ADDRESS_MASK = 0 by decide,
    show (1 : UInt64) &&& BLOCK_ADDRESS_MASK = 0 by decide]
  simp

private theorem blockDescriptor_blockAddress (p : UInt64) :
    blockDescriptor (blockAddress p) = blockDescriptor p := by
  simp only [blockDescriptor_eq, blockAddress, UInt64.and_assoc, UInt64.and_self]

theorem isReadWriteBlock_blockDescriptor (p : UInt64) :
    isReadWriteBlock (blockDescriptor p) = true := by
  simp [isReadWriteBlock, blockAddress_blockDescriptor, blockDescriptor_blockAddress]

theorem typeBits_of_isReadWriteBlock {d : UInt64} (h : isReadWriteBlock d = true) :
    typeBits d = BLOCK := by
  simp only [isReadWriteBlock, beq_iff_eq] at h
  rw [← h]; exact typeBits_blockDescriptor _

theorem typeBits_of_isPlain {d : UInt64} (h : isPlainTableDescriptor d = true) :
    typeBits d = TABLE_OR_PAGE := by
  simp only [isPlainTableDescriptor, beq_iff_eq] at h
  have : typeBits d = (d &&& ~~~ADDRESS_MASK) &&& 3 := by
    simp only [typeBits, UInt64.and_assoc]
    rw [show ~~~ADDRESS_MASK &&& 3 = 3 by decide]
  rw [this, h]; decide

theorem isValid_of_isPlain {d : UInt64} (h : isPlainTableDescriptor d = true) : isValid d = true := by
  simp [isValid, typeBits_of_isPlain h, TABLE_OR_PAGE]

theorem isPlain_of_isReadWriteBlock {d : UInt64} (h : isReadWriteBlock d = true) :
    isPlainTableDescriptor d = false := by
  cases hp : isPlainTableDescriptor d
  · rfl
  · have := (typeBits_of_isPlain hp).symm.trans (typeBits_of_isReadWriteBlock h)
    exact absurd this (by decide)

theorem outputAddress_le (a : UInt64) : (outputAddress a).toNat ≤ a.toNat := by
  rw [outputAddress, UInt64.toNat_and]; exact Nat.and_le_left

theorem blockAddress_le (a : UInt64) : (blockAddress a).toNat ≤ a.toNat := by
  rw [blockAddress, UInt64.toNat_and]; exact Nat.and_le_left

theorem blockAddress_mod (a : UInt64) : (blockAddress a).toNat % BLOCK_SIZE = 0 := by
  have h : blockAddress a &&& 0x1f_ffff = 0 := by
    simp only [blockAddress, UInt64.and_assoc]
    rw [show BLOCK_ADDRESS_MASK &&& 0x1f_ffff = 0 by decide, UInt64.and_zero]
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_and, show (0x1f_ffff : UInt64).toNat = 2 ^ 21 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod] at this
  simpa [BLOCK_SIZE] using this

theorem outputAddress_of_aligned {a : UInt64} (h1 : a.toNat % PAGE_SIZE = 0)
    (h2 : a.toNat < 2 ^ 48) : outputAddress a = a := by
  apply UInt64.toNat_inj.1
  rw [outputAddress, UInt64.toNat_and, show ADDRESS_MASK.toNat = (2 ^ 36 - 1) * 2 ^ 12 by decide]
  obtain ⟨q, hq⟩ : ∃ q, a.toNat = q * 2 ^ 12 := ⟨a.toNat / 4096, by simp [PAGE_SIZE] at h1; omega⟩
  have hq36 : q < 2 ^ 36 := by
    have : q * 4096 < 2 ^ 48 := by rw [← hq]; exact h2
    simp only [Nat.reducePow] at this ⊢; omega
  rw [hq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hb : q.testBit (j - 12) = true
  · have hge := Nat.ge_two_pow_of_testBit hb
    have hlt : j - 12 < 36 := by
      apply Nat.lt_of_not_le; intro hc
      have : 2 ^ 36 ≤ 2 ^ (j - 12) := Nat.pow_le_pow_right (by decide) hc
      omega
    simp [hb, hlt]
  · simp [hb]

theorem direct_or {a : UInt64} (h : a.toNat < VA_LIMIT) :
    (DIRECT_BASE ||| a).toNat = DIRECT_BASE.toNat + a.toNat := by
  rw [UInt64.toNat_or, show DIRECT_BASE.toNat = 2 ^ 39 * (2 ^ 25 - 1) by decide]
  exact (Nat.two_pow_add_eq_or_of_lt h _).symm

private theorem mem_all (k : Kind) : k ∈ Kind.all := by cases k <;> decide

theorem ofPage_isSome_iff (d : UInt64) :
    (Kind.ofPage d).isSome = true ↔ ∃ k, descriptor k (outputAddress d) = d := by
  simp only [Kind.ofPage, List.find?_isSome, beq_iff_eq]
  exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, mem_all k, h⟩⟩

end Krepi.Proofs.PageTables

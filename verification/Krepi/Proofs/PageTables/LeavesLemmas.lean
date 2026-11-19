module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WalkLemmas

/-!
# Page tables: lemmas about the leaves of a set and the addresses of a region

- `upper_decomp`, `exists_upper` and `upper_of_toNat`: an address of the
  upper region on a page is `DIRECT_BASE` and its three indices, and every
  three indices name such an address (`direct_base_toNat` gives the number);
- `mem_leaves`: what an element of `Tables.leaves` is, from the entries of
  the pool.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

theorem direct_base_toNat : DIRECT_BASE.toNat = 18446743523953737728 := by decide

theorem upper_decomp {v : UInt64} (h1 : Region.holds .upper v = true) (h2 : v.toNat % PAGE_SIZE = 0) :
    v.toNat = DIRECT_BASE.toNat + index1 v * GIB_SIZE + index2 v * BLOCK_SIZE +
      index3 v * PAGE_SIZE := by
  simp only [Region.holds, decide_eq_true_eq, direct_base_toNat] at h1
  have := v.toNat_lt
  simp only [index1, index2, index3, GIB_SIZE, BLOCK_SIZE, PAGE_SIZE, ENTRIES, direct_base_toNat] at h2 ⊢
  omega

theorem exists_upper {i j k : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES) (hk : k < ENTRIES) :
    ∃ v : UInt64, v.toNat = DIRECT_BASE.toNat + i * GIB_SIZE + j * BLOCK_SIZE + k * PAGE_SIZE := by
  refine ⟨UInt64.ofNat (DIRECT_BASE.toNat + i * GIB_SIZE + j * BLOCK_SIZE + k * PAGE_SIZE), ?_⟩
  simp only [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  simp only [direct_base_toNat, GIB_SIZE, BLOCK_SIZE, PAGE_SIZE, ENTRIES] at hi hj hk ⊢
  omega

theorem upper_of_toNat {v : UInt64} {i j k : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES)
    (hk : k < ENTRIES)
    (hv : v.toNat = DIRECT_BASE.toNat + i * GIB_SIZE + j * BLOCK_SIZE + k * PAGE_SIZE) :
    Region.holds .upper v = true ∧ v.toNat % PAGE_SIZE = 0 ∧ index1 v = i ∧ index2 v = j ∧
      index3 v = k := by
  simp only [Region.holds, index1, index2, index3, decide_eq_true_eq, hv, direct_base_toNat,
    GIB_SIZE, BLOCK_SIZE, PAGE_SIZE, ENTRIES] at hi hj hk ⊢
  omega

variable {r : Region} {N : Nat}

theorem mem_leaves {s : Tables r N} {base : UInt64} {va : Nat} {form : Form} {d : UInt64} :
    (va, form, d) ∈ s.leaves base ↔
      ∃ i j t2, i < ENTRIES ∧ j < ENTRIES ∧ isValid (s.entry 0 i) = true ∧
        s.child? base (s.entry 0 i) = some t2 ∧ isValid (s.entry t2 j) = true ∧
        (((typeBits (s.entry t2 j) == BLOCK) = true ∧ isReadWriteBlock (s.entry t2 j) = true ∧
            form = .block ∧ d = s.entry t2 j ∧ va = r.first + i * GIB_SIZE + j * BLOCK_SIZE) ∨
          ((typeBits (s.entry t2 j) == BLOCK) = false ∧ ∃ t3 k,
            s.child? base (s.entry t2 j) = some t3 ∧ k < ENTRIES ∧ d = s.entry t3 k ∧
            typeBits d = TABLE_OR_PAGE ∧ (Kind.ofPage d).isSome = true ∧ form = .page ∧
            va = r.first + i * GIB_SIZE + j * BLOCK_SIZE + k * PAGE_SIZE)) := by
  unfold Tables.leaves
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    split at h
    · simp at h
    · rename_i hv1
      split at h
      · simp at h
      · rename_i t2 hc1
        obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
        rw [List.mem_range] at hj
        split at h
        · simp at h
        · rename_i hv2
          split at h
          · rename_i hb
            split at h
            · rename_i hrw
              simp only [List.mem_singleton, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨i, j, t2, hi, hj, by simpa using hv1, hc1, by simpa using hv2,
                Or.inl ⟨hb, hrw, rfl, rfl, rfl⟩⟩
            · simp at h
          · rename_i hb
            split at h
            · simp at h
            · rename_i t3 hc2
              obtain ⟨k, hk, h⟩ := List.mem_filterMap.1 h
              rw [List.mem_range] at hk
              split at h
              · rename_i hk3
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                rw [Bool.and_eq_true, beq_iff_eq] at hk3
                exact ⟨i, j, t2, hi, hj, by simpa using hv1, hc1, by simpa using hv2,
                  Or.inr ⟨by simpa using hb, t3, k, hc2, hk, rfl, hk3.1, hk3.2, rfl, rfl⟩⟩
              · simp at h
  · rintro ⟨i, j, t2, hi, hj, hv1, hc1, hv2, h⟩
    refine ⟨i, hi, ?_⟩
    simp only [hv1, Bool.not_true, Bool.false_eq_true, ite_false, hc1]
    refine List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
    simp only [hv2, Bool.not_true, Bool.false_eq_true, ite_false]
    rcases h with ⟨hb, hrw, rfl, rfl, rfl⟩ | ⟨hb, t3, k, hc2, hk, rfl, h3, hp, rfl, rfl⟩
    · simp [hb, hrw]
    · simp only [hb, Bool.false_eq_true, ite_false, hc2]
      refine List.mem_filterMap.2 ⟨k, List.mem_range.2 hk, ?_⟩
      simp [h3, hp]

end Krepi.Proofs.PageTables

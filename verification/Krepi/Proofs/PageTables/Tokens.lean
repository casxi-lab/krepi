module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Tables
import Krepi.Proofs.PageTables.MapCheckLemmas
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: proofs about the shared state

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the shared state, whose type is
exactly that statement: that the shared state of the boot is well-formed and
keeps the offset of the direct map, that `direct_map` keeps that offset, and
that each transaction keeps the shared state well-formed.

The theorems about the boot and the kernel tables are proved: each
transaction on a kernel set is the entry on that set, whose well-formedness
is a theorem of `Krepi.Proofs.PageTables.Tables`, and leaves the other fields
as they are; every leaf of the direct map after `direct_map` is one of the
set before it or a leaf of a usable range at `DIRECT_BASE | pa`
(`Krepi.Proofs.PageTables.MapWriteLemmas`, `MapCheckLemmas`). The three
theorems about the page ownership table, `newOwnershipSharedWellFormed`,
`withOwnershipWellFormed` and `allocateWellFormed`, are still planned: their
proof is `sorry`, and `verification/statements.json` registers them as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Tokens

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables

/-- A map of a result succeeds exactly when the result is a success. -/
private theorem except_map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

/-- Every entry of the set of `Tables::new` on a zero pool is 0. -/
private theorem new_entry_zero {r : Region} {N : Nat} (t i : Nat) :
    (Tables.new (Pool.zero N) : Tables r N).entry t i = 0 := by
  simp only [Tables.entry, Tables.table, Tables.new, Pool.zero]
  split <;> (try split) <;> simp [Table.zero]

/-- A leaf of the direct map that holds a page keeps the offset of the direct
map. -/
private theorem offset_of_leaf {x : MapLeaf} (hx : DirectLeaf x)
    (hlim : x.pa.toNat + x.form.size ≤ VA_LIMIT) {v : UInt64} {l : Leaf}
    (hv : v.toNat % PAGE_SIZE = 0) (h1 : x.va.toNat ≤ v.toNat) (h2 : v.toNat < x.va.toNat + x.form.size)
    (hp : x.form = .page → l.pa = outputAddress x.desc ∧ Kind.ofPage x.desc = some l.kind)
    (hb : x.form = .block →
      l.pa.toNat = (blockAddress x.desc).toNat + v.toNat % BLOCK_SIZE ∧ l.kind = .readWrite) :
    v = DIRECT_BASE ||| l.pa ∧ l.pa.toNat < VA_LIMIT ∧ l.kind = .readWrite := by
  have hpos := form_size_pos x.form
  have hva := directLeaf_va hx (by omega)
  have h48 : x.pa.toNat < 2 ^ 48 := by simp only [VA_LIMIT] at hlim; omega
  have hD : DIRECT_BASE.toNat % BLOCK_SIZE = 0 := by decide
  cases hfx : x.form
  · obtain ⟨hpa, hk⟩ := hp hfx
    rw [hx.2.2.1 hfx, ofPage_descriptor] at hk
    rw [hx.2.2.1 hfx, outputAddress_descriptor, outputAddress_of_aligned (by
      have := hx.2.1; rw [hfx] at this; exact this) h48] at hpa
    rw [hfx] at h2 hlim
    have hal := hx.2.1; rw [hfx] at hal
    simp only [Form.size] at h2 hlim hal
    have hveq : v = x.va := by
      apply UInt64.toNat_inj.1
      rw [hva] at h1 h2 ⊢
      generalize DIRECT_BASE.toNat = D at h1 h2 hD ⊢
      simp only [PAGE_SIZE, BLOCK_SIZE] at hv hal hD h2 ⊢; omega
    refine ⟨by rw [hveq, hpa, hx.1], by rw [hpa]; omega, ?_⟩
    simp only [Option.some.injEq] at hk; exact hk.symm
  · obtain ⟨hpa, hk⟩ := hb hfx
    have hal := hx.2.1; rw [hfx] at hal
    rw [hx.2.2.2 hfx, blockAddress_blockDescriptor, blockAddress_of_aligned hal h48] at hpa
    rw [hfx] at h2 hlim
    simp only [Form.size] at h2 hlim hal
    have hlt : l.pa.toNat < VA_LIMIT := by
      rw [hva] at h1 h2
      rw [hpa]
      generalize DIRECT_BASE.toNat = D at h1 h2 hD
      simp only [VA_LIMIT, BLOCK_SIZE] at hD hal h2 hlim ⊢; omega
    refine ⟨?_, hlt, hk⟩
    apply UInt64.toNat_inj.1
    rw [direct_or hlt, hpa]
    rw [hva] at h1 h2
    generalize DIRECT_BASE.toNat = D at h1 h2 hD ⊢
    simp only [BLOCK_SIZE] at hD hal h2 ⊢; omega

public theorem bootWellFormed : BootWellFormed := by
  intro E X cfg h1 h2
  refine ⟨Tables.newWellFormed _ _ _ _ h1, Tables.newWellFormed _ _ _ _ h2, ?_⟩
  intro t ht; simp [Shared.boot] at ht

public theorem bootDirectMapOffset : BootDirectMapOffset := by
  intro E X cfg v l hM
  have hw : (Tables.new (Pool.zero DIRECT_MAP_TABLES) : Tables .upper DIRECT_MAP_TABLES).walk
      cfg.directBase v = .ok .root := by
    simp [Tables.walk, Tables.walk2, new_entry_zero, isValid, typeBits, bind, Except.bind, pure,
      Except.pure]
  obtain ⟨-, -, ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩⟩ := hM <;>
    simp only [Shared.boot] at h <;> rw [hw] at h <;> cases h

public theorem buildDirectMapOffset : BuildDirectMapOffset := by
  intro E X cfg cpu s memory s' plan hs hoff h
  unfold Shared.buildDirectMap at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, except_map_ok] at h
    obtain ⟨⟨t, pl⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨leaves, hl, happ, hN, hdl⟩ := directMap_facts hs.2.1 h1
    intro v l hM
    change (t.apply pl).M cfg.directBase v l at hM
    rw [happ] at hM
    rcases final_M hs.2.1 hl hN hM with hM | ⟨q, hq, h1, h2, -, hp, hb⟩
    · exact hoff v l hM
    · obtain ⟨p, hp', -⟩ := placed_leaf hl hq
      obtain ⟨hx, hlim⟩ := hdl _ hp'
      exact offset_of_leaf hx hlim hM.2.1 h1 h2 hp hb

public theorem buildKernelMapWellFormed : BuildKernelMapWellFormed := by
  intro E X cfg cpu s layout s' plan hs h
  unfold Shared.buildKernelMap at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, except_map_ok] at h
    obtain ⟨⟨t, pl⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨Tables.kernelMapWellFormed _ _ _ _ _ _ _ hs.1 h1, hs.2.1, hs.2.2⟩

public theorem buildDirectMapWellFormed : BuildDirectMapWellFormed := by
  intro E X cfg cpu s memory s' plan hs h
  unfold Shared.buildDirectMap at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, except_map_ok] at h
    obtain ⟨⟨t, pl⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hs.1, Tables.directMapWellFormed _ _ _ _ _ _ _ hs.2.1 h1, hs.2.2⟩

public theorem enableWellFormed : EnableWellFormed := by
  intro E X cfg cpu s s' hs h
  unfold Shared.enable at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact hs

public theorem fillKernelWellFormed : FillKernelWellFormed := by
  intro E X cfg tok s v p k s' plan hs h
  unfold Shared.fillKernel at h
  split at h
  · simp only [Option.some.injEq, except_map_ok] at h
    obtain ⟨⟨t, pl⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨Tables.mapPageWellFormed _ _ _ _ _ _ _ _ _ _ hs.1 h1, hs.2.1, hs.2.2⟩
  · simp at h

public theorem newOwnershipSharedWellFormed : NewOwnershipSharedWellFormed := by
  sorry

public theorem withOwnershipWellFormed : WithOwnershipWellFormed := by
  sorry

public theorem allocateWellFormed : AllocateWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Tokens

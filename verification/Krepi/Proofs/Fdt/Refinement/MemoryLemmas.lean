module

public import Krepi.Proofs.Fdt.Refinement.NodePropertyLemmas
public import Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas
public import Krepi.Proofs.Fdt.Refinement.MemorySpecLemmas

/-!
# Device tree: refinement of the memory discovery

The triples of the generated functions of `fdt::discovery`, with `flag_at`
and `has_property` of `fdt::nodes`, stated against
`Krepi.Spec.Fdt.Discovery`, so that the proof of a caller steps over the call
with the triple of the callee and a mutant of a callee fails the proof of the
callee alone. The lemmas that need no generated code are in
`Krepi.Proofs.Fdt.Refinement.MemorySpecLemmas`. A function that writes the
memory map returns its result with the map: its triple relates the result to
the step of the specification through `Agrees`, and on a success the map to
the lists of that step through `MapState`.

- The memory map: `MapState` (the lists and the number of dynamic
  reservations of a memory map in the middle of the discovery),
  `mapState_ram_length`, `no_memory_state` (`NO_MEMORY`) and `mapState_repr`
  (`MemoryMapRepr` at the end); `ram_ranges_spec`, `reserved_regions_spec`,
  `push_reserved_spec` (`pushReserved`) and `add_ram_spec` (`addRam`).
- The entries of a `reg`: `add_ram_entries_loop_spec`, `add_ram_entries_spec`,
  `add_reserved_entries_loop_spec` and `add_reserved_entries_spec`, each on a
  `reg` that `Reg.new` accepted, which `reg_at` checks before.
- The reservation map: `fdtRepr_reservations` (its entries as the 16 bytes of
  each from the start of the view), `add_map_entries_loop_spec` and
  `add_map_entries_spec`.
- Properties and names: `flag_at_spec` (`Node.flag`), `has_property_spec`,
  `nodeRepr_name`, `memory_name_spec` (`isMemoryName`) and the bytes of the
  names that the code writes (`discovery_bytes_memory`,
  `discovery_bytes_device_type`, `discovery_bytes_no_map`,
  `discovery_bytes_reusable`, `discovery_bytes_size`,
  `discovery_path_reserved_memory`).
- RAM: `ram_of_child_spec` (`ramOfChild`), `add_ram_children_loop_spec` and
  `add_ram_children_spec` (the children of the root in tree order).
- Reserved regions: `reserved_of_child_spec` (`reservedOfChild`),
  `add_reserved_children_loop_spec`, `add_reserved_children_spec`,
  `reserved_memory_binding_spec` (`reservedMemoryBinding`) and
  `add_reserved_memory_spec` (`Fdt.reservedMemory`).
- The discovery: `fdt_discover_memory_spec`, the statement
  `FdtDiscoverMemory`, a `@[step]` lemma for the callers of
  `Fdt::discover_memory`.

The children loops walk the nodes with `node_step_spec` of
`Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas`, as `child_named` does: the
invariant is a walker whose walk gives the begin-node tokens from the index
`count` on, and the answer of the fold of the specification over the
children from there on is the answer from the start. A dynamic reservation
adds one to a number that the children before it bound (`reservedOfChild_snd`),
so it never leaves 64 bits.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-- A memory map of the code in the middle of the discovery: its RAM ranges
and reserved regions are the first `ram_count` and `reserved_count` entries of
its arrays, each count within its array, and `dyn` is its number of dynamic
reservations. -/
def MapState (m : fdt.MemoryMap) (ram : List Span) (res : List ReservedRegion) (dyn : Nat) :
    Prop :=
  m.ram_count.val ≤ MAX_MEMORY_REGIONS.toNat ∧ m.reserved_count.val ≤ MAX_RESERVED_REGIONS.toNat ∧
    (m.ram.val.take m.ram_count.val).map spanOf = ram ∧
    (m.reserved.val.take m.reserved_count.val).map regionOf = res ∧ m.dynamic.val = dyn

/-- `RAM_RANGES`: `MAX_MEMORY_REGIONS` as a `usize`. -/
@[step] theorem ram_ranges_spec : fdt.RAM_RANGES ⦃ n => n.val = MAX_MEMORY_REGIONS.toNat ⦄ := by
  unfold fdt.RAM_RANGES
  refine spec_of_eq rfl ?_
  rw [UScalar.cast_val_eq, fdt.MAX_MEMORY_REGIONS]
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits :=
    Nat.pow_le_pow_right (by omega) usize_numBits_ge
  exact Nat.mod_eq_of_lt (by show 32 < _; omega)

/-- `RESERVED_REGIONS`: `MAX_RESERVED_REGIONS` as a `usize`. -/
@[step] theorem reserved_regions_spec :
    fdt.RESERVED_REGIONS ⦃ n => n.val = MAX_RESERVED_REGIONS.toNat ⦄ := by
  unfold fdt.RESERVED_REGIONS
  refine spec_of_eq rfl ?_
  rw [UScalar.cast_val_eq, fdt.MAX_RESERVED_REGIONS]
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits :=
    Nat.pow_le_pow_right (by omega) usize_numBits_ge
  exact Nat.mod_eq_of_lt (by show 128 < _; omega)

/-- `push_reserved(map, region)`: `pushReserved`, the region after the others,
or `LimitExceeded` beyond `MAX_RESERVED_REGIONS`. -/
@[step] theorem push_reserved_spec {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) (region : fdt.ReservedRegion) :
    fdt.discovery.push_reserved m region ⦃ r m' =>
      Agrees (fun _ res' => MapState m' ram res' dyn) errorOf r
        (pushReserved res (regionOf region)) ⦄ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  have hl : m.reserved.val.length = 128 := by simp
  have hres : res.length = m.reserved_count.val := by
    rw [← h4, List.length_map, List.length_take, hl]
    simp only [MAX_RESERVED_REGIONS, UInt64.reduceToNat] at h2; omega
  unfold fdt.discovery.push_reserved
  step with reserved_regions_spec as ⟨i, i_post⟩
  simp only [MAX_RESERVED_REGIONS, UInt64.reduceToNat] at i_post h2
  by_cases hc : m.reserved_count ≥ i
  · simp only [hc, ↓reduceIte, spec_ok]
    have : MAX_RESERVED_REGIONS.toNat < res.length + 1 := by
      simp only [MAX_RESERVED_REGIONS, UInt64.reduceToNat]; scalar_tac
    simp only [pushReserved, this, ↓reduceIte]
    rfl
  · simp only [hc, ↓reduceIte]
    have : ¬ MAX_RESERVED_REGIONS.toNat < res.length + 1 := by
      simp only [MAX_RESERVED_REGIONS, UInt64.reduceToNat]; scalar_tac
    simp only [pushReserved, this, ↓reduceIte]
    step*
    refine ⟨h1, by simp only [MAX_RESERVED_REGIONS, UInt64.reduceToNat]; scalar_tac, h3, ?_, h5⟩
    rw [a_post, i1_post, Array.set_val_eq, take_set_succ _ (by rw [hl]; scalar_tac) _,
      List.map_append, h4]
    rfl

/-- The number of RAM ranges of a memory map is its count. -/
theorem mapState_ram_length {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) : ram.length = m.ram_count.val := by
  obtain ⟨h1, -, h3, -⟩ := hm
  have hl : m.ram.val.length = 32 := by simp
  rw [← h3, List.length_map, List.length_take, hl]
  simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat] at h1; omega

/-- `add_ram(map, span)`: `addRam`, the range after the others, or the error of
the first broken rule. -/
@[step] theorem add_ram_spec {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) (span : fdt.Span) :
    fdt.discovery.add_ram m span ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r (addRam ram (spanOf span)) ⦄ := by
  have hlen := mapState_ram_length hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  have hl : m.ram.val.length = 32 := by simp
  simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat] at h1
  unfold fdt.discovery.add_ram
  by_cases hz : span.size = 0#u64
  · simp only [hz, ↓reduceIte, spec_ok]
    have : (spanOf span).size = 0 := by rw [spanOf_size, word64_eq_zero_iff]; exact hz
    simp only [addRam, this, ↓reduceIte]
    rfl
  · simp only [hz, ↓reduceIte, lift, bind_ok]
    have hz' : ¬ (spanOf span).size = 0 := by rw [spanOf_size, word64_eq_zero_iff]; exact hz
    step as ⟨s1, s1_post⟩
    step as ⟨b, b_post⟩
    have hb : b = ram.any (·.touches (spanOf span)) := by
      rw [b_post, ← h3, spansOf, s1_post, Array.val_to_slice, List.map_take]
    by_cases hb' : b = true
    · simp only [hb', ↓reduceIte, spec_ok]
      simp only [addRam, hz', ↓reduceIte, ← hb, hb']
      rfl
    · simp only [hb', Bool.false_eq_true, ↓reduceIte]
      step with ram_ranges_spec as ⟨i, i_post⟩
      simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat] at i_post
      have hb2 : (ram.any (·.touches (spanOf span))) = false := by rw [← hb]; simpa using hb'
      by_cases hc : m.ram_count ≥ i
      · simp only [hc, ↓reduceIte, spec_ok]
        have : MAX_MEMORY_REGIONS.toNat < ram.length + 1 := by
          simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat]; scalar_tac
        simp only [addRam, hz', hb2, this, ↓reduceIte, Bool.false_eq_true]
        rfl
      · simp only [hc, ↓reduceIte]
        have : ¬ MAX_MEMORY_REGIONS.toNat < ram.length + 1 := by
          simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat]; scalar_tac
        simp only [addRam, hz', hb2, this, ↓reduceIte, Bool.false_eq_true]
        step*
        refine ⟨by simp only [MAX_MEMORY_REGIONS, UInt64.reduceToNat]; scalar_tac, h2, ?_, h4, h5⟩
        rw [a_post, i1_post, Array.set_val_eq, take_set_succ _ (by rw [hl]; scalar_tac) _,
          List.map_append, h3]
        rfl

/-- The loop of `add_ram_entries`: from an entry at a multiple of the stride,
whose entries from there on `regEntry` reads as `l`, the RAM ranges after
`addRam` of each of `l`. -/
theorem add_ram_entries_loop_spec (bytes : Slice U8) (ac sc : U32) (stride : Usize)
    (hs : stride.val = (ac.val + sc.val) * 4) (h0 : 0 < stride.val)
    (hd : bytes.length % stride.val = 0) {res : List ReservedRegion} {dyn : Nat}
    (E : Except Krepi.Spec.Fdt.Error (List Span))
    (m : fdt.MemoryMap) (pos : Usize) (ram : List Span) (l : List Span)
    (hp : pos.val % stride.val = 0) (hpl : pos.val ≤ bytes.length)
    (hl : (chunks (bytesOf bytes) stride.val ((bytes.length - pos.val) / stride.val) pos.val).mapM
      (regEntry (word32 ac) (word32 sc)) = .ok l)
    (hm : MapState m ram res dyn) (hE : l.foldlM addRam ram = E) :
    fdt.discovery.add_ram_entries_loop m bytes ac sc stride pos ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r E ⦄ := by
  unfold fdt.discovery.add_ram_entries_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryMap × Usize) => bytes.length - x.2.val)
    (inv := fun (x : fdt.MemoryMap × Usize) => ∃ ram l, x.2.val % stride.val = 0 ∧
      x.2.val ≤ bytes.length ∧
      (chunks (bytesOf bytes) stride.val ((bytes.length - x.2.val) / stride.val) x.2.val).mapM
        (regEntry (word32 ac) (word32 sc)) = .ok l ∧
      MapState x.1 ram res dyn ∧ l.foldlM addRam ram = E)
  · rintro ⟨m, pos⟩ ⟨ram, l, hp, hpl, hl, hm, hE⟩
    simp only at hp hpl hl hm hE
    unfold fdt.discovery.add_ram_entries_loop.body
    simp only
    by_cases hlt : pos < Slice.len bytes
    · simp only [hlt, ↓reduceIte]
      have hlt' : pos.val < bytes.length := slice_lt_len hlt
      have hle : pos.val + stride.val ≤ bytes.length := add_stride_le hp hd hlt'
      rw [chunks_cons h0 hle] at hl
      obtain ⟨sp, l', rfl, hsp, hl'⟩ := mapM_cons_eq_ok hl
      step with reg_entry_spec bytes pos ac sc (by rw [← hs]; exact hle) as ⟨r, r_post⟩
      rw [← hs, hsp] at r_post
      cases r with
      | Err e => exact r_post.elim
      | Ok val =>
        have hv : spanOf val = sp := r_post
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with add_ram_spec hm val as ⟨r1, m1, hr1⟩
        rw [List.foldlM_cons] at hE
        rw [hv] at hr1
        cases r1 with
        | Err e =>
          have he : addRam ram sp = .error (errorOf e) := agrees_err_iff.mp hr1
          simp only [bind_ok]
          step with from_residual_spec e as ⟨r2, hr2⟩
          rw [hr2, ← hE, he]
          rfl
        | Ok u =>
          obtain ⟨ram1, hram1, hm1⟩ := agrees_ok_iff.mp hr1
          simp only [bind_ok]
          step as ⟨at1, at1_post⟩
          refine ⟨⟨ram1, l', ?_, ?_, ?_, hm1, ?_⟩, ?_⟩
          · rw [at1_post, Nat.add_mod_right]; exact hp
          · rw [at1_post]; exact hle
          · rw [at1_post]; exact hl'
          · rw [← hE, hram1]; rfl
          · rw [at1_post]; omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge := slice_len_le hlt
      rw [chunks_nil h0 (by omega)] at hl
      cases hl
      rw [← hE]
      exact hm
  · exact ⟨ram, l, hp, hpl, hl, hm, hE⟩

/-- `add_ram_entries(map, bytes, address_cells, size_cells)` on a `reg` that
`Reg.new` accepted: `addRam` of each of its entries in order. -/
theorem add_ram_entries_spec {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) (bytes : Slice U8) (ac sc : U32) {R : Reg}
    (hR : Reg.new (bytesOf bytes) (word32 ac) (word32 sc) = .ok R) :
    fdt.discovery.add_ram_entries m bytes ac sc ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r
        (R.entries.foldlM addRam ram) ⦄ := by
  obtain ⟨hac, hsc, hne, hmod, hmap⟩ := regNew_ok hR
  rw [bytesOf_size] at hne hmod hmap
  unfold fdt.discovery.add_ram_entries
  step with reg_stride_spec ac sc (by omega) as ⟨stride, hs⟩
  exact add_ram_entries_loop_spec bytes ac sc stride hs (by omega) (by rw [hs]; exact hmod) _ m
    0#usize ram R.entries (by simp) (by simp) (by rw [hs]; simpa using hmap) hm rfl

/-- The loop of `add_reserved_entries`: from an entry at a multiple of the
stride, whose entries from there on `regEntry` reads as `l`, the reserved
regions after `addReservedSpan` of each of `l`. -/
theorem add_reserved_entries_loop_spec (bytes : Slice U8) (ac sc : U32) (noMap reusable : Bool)
    (stride : Usize) (hs : stride.val = (ac.val + sc.val) * 4) (h0 : 0 < stride.val)
    (hd : bytes.length % stride.val = 0) {ram : List Span} {dyn : Nat}
    (E : Except Krepi.Spec.Fdt.Error (List ReservedRegion))
    (m : fdt.MemoryMap) (pos : Usize) (res : List ReservedRegion) (l : List Span)
    (hp : pos.val % stride.val = 0) (hpl : pos.val ≤ bytes.length)
    (hl : (chunks (bytesOf bytes) stride.val ((bytes.length - pos.val) / stride.val) pos.val).mapM
      (regEntry (word32 ac) (word32 sc)) = .ok l)
    (hm : MapState m ram res dyn) (hE : l.foldlM (addReservedSpan noMap reusable) res = E) :
    fdt.discovery.add_reserved_entries_loop m bytes ac sc noMap reusable stride pos ⦃ r m' =>
      Agrees (fun _ res' => MapState m' ram res' dyn) errorOf r E ⦄ := by
  unfold fdt.discovery.add_reserved_entries_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryMap × Usize) => bytes.length - x.2.val)
    (inv := fun (x : fdt.MemoryMap × Usize) => ∃ res l, x.2.val % stride.val = 0 ∧
      x.2.val ≤ bytes.length ∧
      (chunks (bytesOf bytes) stride.val ((bytes.length - x.2.val) / stride.val) x.2.val).mapM
        (regEntry (word32 ac) (word32 sc)) = .ok l ∧
      MapState x.1 ram res dyn ∧ l.foldlM (addReservedSpan noMap reusable) res = E)
  · rintro ⟨m, pos⟩ ⟨res, l, hp, hpl, hl, hm, hE⟩
    simp only at hp hpl hl hm hE
    unfold fdt.discovery.add_reserved_entries_loop.body
    simp only
    by_cases hlt : pos < Slice.len bytes
    · simp only [hlt, ↓reduceIte]
      have hlt' : pos.val < bytes.length := slice_lt_len hlt
      have hle : pos.val + stride.val ≤ bytes.length := add_stride_le hp hd hlt'
      rw [chunks_cons h0 hle] at hl
      obtain ⟨sp, l', rfl, hsp, hl'⟩ := mapM_cons_eq_ok hl
      step with reg_entry_spec bytes pos ac sc (by rw [← hs]; exact hle) as ⟨r, r_post⟩
      rw [← hs, hsp] at r_post
      cases r with
      | Err e => exact r_post.elim
      | Ok val =>
        have hv : spanOf val = sp := r_post
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        rw [List.foldlM_cons] at hE
        by_cases hz : val.size = 0#u64
        · simp only [hz, ↓reduceIte, spec_ok]
          have : sp.size = 0 := by rw [← hv, spanOf_size, word64_eq_zero_iff]; exact hz
          rw [← hE]
          simp only [addReservedSpan, this, ↓reduceIte]
          rfl
        · simp only [hz, ↓reduceIte]
          have hz' : ¬ sp.size = 0 := by rw [← hv, spanOf_size, word64_eq_zero_iff]; exact hz
          simp only [addReservedSpan, hz', ↓reduceIte] at hE
          step with push_reserved_spec hm { span := val, no_map := noMap, reusable := reusable }
            as ⟨r1, m1, hr1⟩
          have hreg : regionOf { span := val, no_map := noMap, reusable := reusable } =
              ⟨sp, noMap, reusable⟩ := by rw [regionOf, hv]
          rw [hreg] at hr1
          cases r1 with
          | Err e =>
            have he := agrees_err_iff.mp hr1
            simp only [bind_ok]
            step with from_residual_spec e as ⟨r2, hr2⟩
            rw [hr2, ← hE, he]
            rfl
          | Ok u =>
            obtain ⟨res1, hres1, hm1⟩ := agrees_ok_iff.mp hr1
            simp only [bind_ok]
            step as ⟨at1, at1_post⟩
            refine ⟨⟨res1, l', ?_, ?_, ?_, hm1, ?_⟩, ?_⟩
            · rw [at1_post, Nat.add_mod_right]; exact hp
            · rw [at1_post]; exact hle
            · rw [at1_post]; exact hl'
            · rw [← hE, hres1]; rfl
            · rw [at1_post]; omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge := slice_len_le hlt
      rw [chunks_nil h0 (by omega)] at hl
      cases hl
      rw [← hE]
      exact hm
  · exact ⟨res, l, hp, hpl, hl, hm, hE⟩

/-- `add_reserved_entries(map, bytes, address_cells, size_cells, no_map,
reusable)` on a `reg` that `Reg.new` accepted: `addReservedSpan` of each of
its entries in order. -/
theorem add_reserved_entries_spec {m : fdt.MemoryMap} {ram : List Span}
    {res : List ReservedRegion} {dyn : Nat} (hm : MapState m ram res dyn) (bytes : Slice U8)
    (ac sc : U32) (noMap reusable : Bool) {R : Reg}
    (hR : Reg.new (bytesOf bytes) (word32 ac) (word32 sc) = .ok R) :
    fdt.discovery.add_reserved_entries m bytes ac sc noMap reusable ⦃ r m' =>
      Agrees (fun _ res' => MapState m' ram res' dyn) errorOf r
        (R.entries.foldlM (addReservedSpan noMap reusable) res) ⦄ := by
  obtain ⟨hac, hsc, hne, hmod, hmap⟩ := regNew_ok hR
  rw [bytesOf_size] at hne hmod hmap
  unfold fdt.discovery.add_reserved_entries
  step with reg_stride_spec ac sc (by omega) as ⟨stride, hs⟩
  exact add_reserved_entries_loop_spec bytes ac sc noMap reusable stride hs (by omega)
    (by rw [hs]; exact hmod) _ m 0#usize res R.entries (by simp) (by simp)
    (by rw [hs]; simpa using hmap) hm rfl

/-- The entries of the reservation map of a tree of the code: 16 bytes each,
read from the start of its view. -/
theorem fdtRepr_reservations {t : fdt.Fdt} {T : Fdt} (hR : FdtRepr t T) :
    t.reservations.length = 16 * T.reservations.length ∧
      ReadsAt (bytesOf t.reservations) 0 T.reservations := by
  obtain ⟨hp, h, hh, -, -, -, hres⟩ := hR
  have F := header_facts hh
  obtain ⟨hread, hlen⟩ := reservationMap_ok (parse_ok hp hh).1
  have hle : h.layout.reserveStart + 16 * T.reservations.length ≤ h.blob.size := by
    rw [F.blob_size]; omega
  have hsz : (bytesOf t.reservations).size = 16 * T.reservations.length := by
    rw [hres, ByteArray.size_extract]; omega
  rw [bytesOf_size] at hsz
  refine ⟨hsz, ?_⟩
  rw [hres]
  exact readsAt_extract hread (Nat.le_refl _) hle

/-- The loop of `add_map_entries`: from a cursor whose entries from there on
are `l`, the reserved regions after `pushReserved` of each of `l`, with
`no-map` set and `reusable` clear. -/
theorem add_map_entries_loop_spec (entries : Slice U8) {ram : List Span} {dyn : Nat}
    (E : Except Krepi.Spec.Fdt.Error (List ReservedRegion))
    (m : fdt.MemoryMap) (pos : Usize) (res : List ReservedRegion) (l : List Span)
    (hl : entries.length = pos.val + 16 * l.length) (hr : ReadsAt (bytesOf entries) pos.val l)
    (hm : MapState m ram res dyn)
    (hE : l.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) res = E) :
    fdt.discovery.add_map_entries_loop m entries pos ⦃ r m' =>
      Agrees (fun _ res' => MapState m' ram res' dyn) errorOf r E ⦄ := by
  unfold fdt.discovery.add_map_entries_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryMap × Usize) => entries.length - x.2.val)
    (inv := fun (x : fdt.MemoryMap × Usize) => ∃ res l,
      entries.length = x.2.val + 16 * l.length ∧ ReadsAt (bytesOf entries) x.2.val l ∧
      MapState x.1 ram res dyn ∧
      l.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) res = E)
  · rintro ⟨m, pos⟩ ⟨res, l, hl, hr, hm, hE⟩
    simp only at hl hr hm hE
    unfold fdt.discovery.add_map_entries_loop.body
    simp only
    by_cases hlt : pos < Slice.len entries
    · simp only [hlt, ↓reduceIte]
      have hlt' : pos.val < entries.length := slice_lt_len hlt
      cases l with
      | nil => rw [List.length_nil, Nat.mul_zero, Nat.add_zero] at hl; omega
      | cons sp l' =>
      obtain ⟨⟨hs1, hs2⟩, hr'⟩ := readsAt_cons.mp hr
      rw [List.length_cons] at hl
      rw [List.foldlM_cons] at hE
      step with u64_at_spec entries pos as ⟨r, r_post⟩
      rw [hs1] at r_post
      cases r with
      | Err e => exact r_post.elim
      | Ok v =>
        have hv : word64 v = sp.start := r_post
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨i1, i1_post⟩
        step with u64_at_spec entries i1 as ⟨r1, r1_post⟩
        rw [i1_post, hs2] at r1_post
        cases r1 with
        | Err e => exact r1_post.elim
        | Ok v1 =>
          have hv1 : word64 v1 = sp.size := r1_post
          simp only [bind_ok]
          step with push_reserved_spec hm ⟨⟨v, v1⟩, true, false⟩ as ⟨r2, m2, hr2⟩
          have hreg : regionOf ⟨⟨v, v1⟩, true, false⟩ = ⟨sp, true, false⟩ := by
            rw [regionOf, spanOf, hv, hv1]
          rw [hreg] at hr2
          cases r2 with
          | Err e =>
            have he := agrees_err_iff.mp hr2
            simp only [bind_ok]
            step with from_residual_spec e as ⟨r3, hr3⟩
            rw [hr3, ← hE, he]
            rfl
          | Ok u =>
            obtain ⟨res1, hres1, hm1⟩ := agrees_ok_iff.mp hr2
            simp only [bind_ok]
            step as ⟨at1, at1_post⟩
            refine ⟨⟨res1, l', ?_, ?_, hm1, ?_⟩, ?_⟩
            · rw [at1_post]; omega
            · rw [at1_post]; exact hr'
            · rw [← hE, hres1]; rfl
            · rw [at1_post]; omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge := slice_len_le hlt
      cases l with
      | cons _ _ => rw [List.length_cons] at hl; omega
      | nil =>
        rw [← hE]
        exact hm
  · exact ⟨res, l, hl, hr, hm, hE⟩

/-- `add_map_entries(map, entries)`: the entries of the reservation map, each
with `pushReserved`. -/
theorem add_map_entries_spec {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) (entries : Slice U8) (l : List Span)
    (hl : entries.length = 16 * l.length) (hr : ReadsAt (bytesOf entries) 0 l) :
    fdt.discovery.add_map_entries m entries ⦃ r m' =>
      Agrees (fun _ res' => MapState m' ram res' dyn) errorOf r
        (l.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) res) ⦄ := by
  unfold fdt.discovery.add_map_entries
  exact add_map_entries_loop_spec entries _ m 0#usize res l (by simpa using hl) hr hm rfl

/-! ## Flags and properties -/

/-- `flag_at(structure, strings, node, name)`: `Node.flag` of the property
named as the bytes of `s`. -/
theorem flag_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» : Slice U8) (s : String) (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.flag_at t.structure t.strings a «name» ⦃ r =>
      Agrees (· = ·) errorOf r (N.flag s) ⦄ := by
  unfold fdt.nodes.flag_at
  step with value_at_spec hu h «name» s hk as ⟨o, ho⟩
  rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
  · simp only [Node.flag, hv, spec_ok]; rfl
  · exact ho.elim
  · exact ho.elim
  · obtain ⟨h1, h2, h3⟩ := ho
    dsimp only at h1 h2 h3
    have hsz : v.size = en.val - st.val := by
      rw [← h3, ByteArray.size_extract, bytesOf_size, Nat.min_eq_left h2]
    simp only [uncurry_apply_pair]
    by_cases he : st = en
    · simp only [he, ↓reduceIte, spec_ok, Node.flag, hv]
      have : v.size = 0 := by rw [hsz, he]; omega
      simp only [this, ↓reduceIte]; rfl
    · simp only [he, ↓reduceIte, spec_ok, Node.flag, hv]
      have : ¬ v.size = 0 := by
        rw [hsz]; intro h0; exact he (UScalar.eq_of_val_eq (by omega))
      simp only [this, ↓reduceIte]; rfl

/-- `has_property(structure, strings, node, name)`: whether the node has the
property named as the bytes of `s`. -/
theorem has_property_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» : Slice U8) (s : String) (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.has_property t.structure t.strings a «name» ⦃ b => b = (N.property s).isSome ⦄ := by
  unfold fdt.nodes.has_property
  step with value_at_spec hu h «name» s hk as ⟨o, ho⟩
  rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
  · simp only [spec_ok]; rfl
  · exact ho.elim
  · exact ho.elim
  · simp only [spec_ok]; rfl

/-! ## Names -/

/-- The bytes of the name `memory` that the code writes. -/
theorem discovery_bytes_memory :
    bytesOf (Array.to_slice (Array.make 6#usize [109#u8, 101#u8, 109#u8, 111#u8, 114#u8, 121#u8])) =
      "memory".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- The bytes of the name `device_type` that the code writes. -/
theorem discovery_bytes_device_type :
    bytesOf (Array.to_slice (Array.make 11#usize [100#u8, 101#u8, 118#u8, 105#u8, 99#u8, 101#u8,
      95#u8, 116#u8, 121#u8, 112#u8, 101#u8])) = "device_type".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- The name of a node of a tree: its bytes within the structure block. -/
theorem nodeRepr_name (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    a.name_start.val ≤ a.name_end.val ∧ a.name_end.val ≤ t.structure.length ∧
      (bytesOf t.structure).extract a.name_start.val a.name_end.val = N.name.toUTF8 := by
  obtain ⟨L, ht, hk, ⟨-, -, h3, h4, -⟩, hn, next, hd⟩ := nodeRepr_begin hu h
  obtain ⟨hnext, hex, hle⟩ := decodeToken_begin hd
  have := le_align4 (L[N.index.val].offset + 4 + N.name.utf8ByteSize + 1)
  rw [bytesOf_size] at hle
  rw [hn] at h4
  dsimp only at h3 h4 hle
  refine ⟨by omega, by omega, ?_⟩
  rw [h3, h4, hex, String.toUTF8_eq_toByteArray]

/-- `memory_name(structure, start, end)` at the name of a node:
`isMemoryName` of the name. -/
theorem memory_name_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.discovery.memory_name t.structure a.name_start a.name_end ⦃ b =>
      b = isMemoryName N.name ⦄ := by
  obtain ⟨h1, h2, hx⟩ := nodeRepr_name hu h
  unfold fdt.discovery.memory_name
  simp only [lift, bind_ok]
  step as ⟨b, b_post⟩
  rw [isMemoryName_eq]
  have hb : b = decide (N.name = "memory") := by
    rw [b_post, hx, discovery_bytes_memory, decide_eq_decide, ← toByteArray_eq_toUTF8,
      ← String.toUTF8_eq_toByteArray]
    exact ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩
  by_cases hm : N.name = "memory"
  · simp only [hb, hm, decide_true, ↓reduceIte, Bool.true_or, spec_ok]
  · simp only [hb, hm, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    step as ⟨b1, b1_post⟩
    rw [b1_post, Bool.eq_iff_iff, decide_eq_true_iff, isPrefixOf_iff_take]
    have hl : ((bytesOf t.structure).extract a.name_start.val a.name_end.val).toList =
        N.name.toUTF8.toList := by rw [hx]
    rw [bytesOf_extract] at hl
    have hp : (bytesOf (Array.to_slice (Array.make 7#usize
        [109#u8, 101#u8, 109#u8, 111#u8, 114#u8, 121#u8, 64#u8]))).toList =
        [109, 101, 109, 111, 114, 121, 64] := by rw [bytesOf_toList]; rfl
    rw [← hl, byteArray_eq_iff, bytesOf_extract, hp]
    have hn7 : (Array.to_slice (Array.make 7#usize
        [109#u8, 101#u8, 109#u8, 111#u8, 114#u8, 121#u8, 64#u8])).length = 7 := by simp
    rw [hn7, Nat.add_sub_cancel_left, ← List.map_take, List.take_take]
    constructor
    · rintro ⟨-, -, h7, he⟩
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        List.length_cons, List.length_cons, List.length_singleton, Nat.min_eq_left h7]
      exact he
    · intro he
      have h7 : 7 ≤ a.name_end.val - a.name_start.val := by
        have := congrArg List.length he
        simp only [List.length_map, List.length_take, List.length_cons, List.length_nil] at this
        omega
      refine ⟨h1, h2, h7, ?_⟩
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        List.length_cons, List.length_cons, List.length_singleton, Nat.min_eq_left h7] at he
      exact he

/-! ## RAM -/

/-- `ram_of_child(map, structure, strings, node)`: `ramOfChild` of the RAM
ranges of the map and the node. -/
theorem ram_of_child_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) :
    fdt.discovery.ram_of_child m t.structure t.strings a ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r (ramOfChild ram N) ⦄ := by
  unfold fdt.discovery.ram_of_child
  simp only [lift, bind_ok]
  step with string_at_spec hu h _ "device_type" discovery_bytes_device_type as ⟨r, r_post⟩
  rw [ramOfChild_eq]
  refine try_state_spec r_post (fun e => from_residual_state_spec e m) fun o dt hodt _ => ?_
  simp only
  step with memory_name_spec hu h as ⟨byName, hbn⟩
  apply WP.spec_bind (Pₘ := fun b => b = (dt == some "memory"))
  · rcases o with _ | ⟨st, en⟩ <;> rcases dt with _ | str
    · exact spec_of_eq rfl rfl
    · exact hodt.elim
    · exact hodt.elim
    · obtain ⟨h1, h2, h3⟩ := hodt
      simp only [uncurry_apply_pair]
      step as ⟨b, b_post⟩
      rw [b_post, h3, discovery_bytes_memory]
      by_cases hs : str = "memory"
      · rw [hs, decide_eq_true ⟨h1, h2, rfl⟩]; rfl
      · rw [decide_eq_false fun h => hs (toByteArray_eq_toUTF8.1
          (by rw [← String.toUTF8_eq_toByteArray]; exact h.2.2))]
        exact (beq_false_of_ne fun e => hs (Option.some.inj e)).symm
  · intro byType hbt
    subst hbn hbt
    cases hn : isMemoryName N.name <;> cases hty : (dt == some "memory") <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true, Bool.not_false,
        Bool.not_true, Bool.and_true, Bool.and_false]
    · exact spec_of_eq rfl hm
    all_goals
      step with enabled_at_spec hu h as ⟨r1, r1_post⟩
      refine try_state_spec r1_post (fun e => from_residual_state_spec e m) fun v en hv _ => ?_
      subst hv
      cases v <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
      · exact spec_of_eq rfl hm
    · exact spec_of_eq rfl rfl
    · exact spec_of_eq rfl rfl
    · step with reg_at_spec hu h as ⟨r2, r2_post⟩
      refine try_state_spec r2_post (fun e => from_residual_state_spec e m) fun g R hg _ => ?_
      obtain ⟨g1, g2, hR⟩ := hg
      simp only
      step as ⟨s1, s1_post⟩
      rw [← bytesOf_of_slice s1_post] at hR
      exact add_ram_entries_spec hm s1 _ _ hR

/-- The loop of `add_ram_children`: from a walker at the node of index
`count`, `ramOfChild` of each child of the root from there on. -/
theorem add_ram_children_loop_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {p : Nat} (hp : p < T.records.size) {root : fdt.NodeAt}
    (hroot : AtRepr root (L[p]'(ht.length ▸ hp))) {res : List ReservedRegion} {dyn : Nat}
    (E : Except Krepi.Spec.Fdt.Error (List Span)) (m : fdt.MemoryMap) (w : fdt.Walker)
    (count : Usize) (f : Nat) (st : List Nat) (ram : List Span)
    (hw : WalkerRepr w st) (hf : f ≤ MAX_TOKENS.toNat) (hc : count.val ≤ L.length)
    (hL : nodesFrom (bytesOf t.structure) (bytesOf t.strings) f w.cursor.val st =
      some (L.drop count.val))
    (hm : MapState m ram res dyn)
    (hE : ((T.nodes.drop count.val).filter (·.isChildOf ⟨T, ⟨p, hp⟩⟩)).foldlM ramOfChild ram = E) :
    fdt.discovery.add_ram_children_loop m t.structure t.strings root w count ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r E ⦄ := by
  have hlen := ht.length
  have hmax : L.length < MAX_TOKENS.toNat := (nodesFrom_sorted ht.walk).2.2
  rw [show MAX_TOKENS.toNat = 65536 from rfl] at hmax
  unfold fdt.discovery.add_ram_children_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryMap × fdt.Walker × Usize) => L.length - x.2.2.val)
    (inv := fun (x : fdt.MemoryMap × fdt.Walker × Usize) => ∃ f st ram,
      WalkerRepr x.2.1 st ∧ f ≤ MAX_TOKENS.toNat ∧ x.2.2.val ≤ L.length ∧
      nodesFrom (bytesOf t.structure) (bytesOf t.strings) f x.2.1.cursor.val st =
        some (L.drop x.2.2.val) ∧ MapState x.1 ram res dyn ∧
      ((T.nodes.drop x.2.2.val).filter (·.isChildOf ⟨T, ⟨p, hp⟩⟩)).foldlM ramOfChild ram = E)
  · rintro ⟨m, w, count⟩ ⟨f, st, ram, hw, hf, hc, hL, hm, hE⟩
    simp only at hw hc hL hm hE
    unfold fdt.discovery.add_ram_children_loop.body
    step
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post
    refine ite_spec_pos (by scalar_tac) ?_
    rcases Nat.lt_or_ge count.val L.length with hlt | hge
    · have hk : count.val < T.records.size := by omega
      rw [List.drop_eq_getElem_cons hlt] at hL
      have hdrop : T.nodes.drop count.val =
          ⟨T, ⟨count.val, hk⟩⟩ :: T.nodes.drop (count.val + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [nodes_length]; exact hk), nodes_getElem]
      rw [hdrop] at hE
      step with node_step_spec t.structure (bytesOf t.strings) w f st _ ht.size hw hf hL
      obtain ⟨⟨f', st', hf', hw', hL'⟩, a, ha, hat⟩ := next_post
      dsimp only at ha hL' hw'
      subst ha
      simp only
      step
      have hchild := ht.child_iff hk hp hat hroot
      have hN := (ht.nodeRepr_iff a count.val hk).2 hat
      by_cases hb : b = true
      · refine ite_spec_pos hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = true := by
          rw [← hchild, ← b_post]; exact hb
        simp only [List.filter_cons, hc1, ↓reduceIte, List.foldlM_cons] at hE
        step with ram_of_child_spec hu hN hm as ⟨r1, m1, hr1⟩
        cases r1 with
        | Err e =>
          have he := agrees_err_iff.mp hr1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with from_residual_spec e as ⟨r2, hr2⟩
          rw [hr2, ← hE, he]
          rfl
        | Ok u =>
          obtain ⟨ram1, hram1, hm1⟩ := agrees_ok_iff.mp hr1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step as ⟨count1, count1_post⟩
          refine ⟨⟨f', st', ram1, hw', hf', by scalar_tac, by simpa [count1_post] using hL', hm1,
            ?_⟩, by scalar_tac⟩
          rw [count1_post, ← hE, hram1]; rfl
      · refine ite_spec_neg hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = false := by
          rw [← hchild, ← b_post]; simpa using hb
        simp only [List.filter_cons, hc1, Bool.false_eq_true, ↓reduceIte] at hE
        step as ⟨count1, count1_post⟩
        exact ⟨⟨f', st', ram, hw', hf', by scalar_tac, by simpa [count1_post] using hL', hm,
          by rw [count1_post]; exact hE⟩, by scalar_tac⟩
    · rw [List.drop_of_length_le hge] at hL
      step with node_step_spec t.structure (bytesOf t.strings) w f st [] ht.size hw hf hL
      obtain ⟨-, hnone, -⟩ := next_post
      dsimp only at hnone
      subst hnone
      simp only [spec_ok]
      rw [List.drop_of_length_le (by rw [nodes_length]; omega), List.filter_nil,
        List.foldlM_nil] at hE
      rw [← hE]
      exact hm
  · exact ⟨f, st, ram, hw, hf, hc, hL, hm, hE⟩

/-- `add_ram_children(map, structure, strings, root)`: `ramOfChild` of each
child of the root in tree order. -/
theorem add_ram_children_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {root : fdt.NodeAt} {R : Node} (hR : NodeRepr ⟨t, root⟩ R)
    {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion} {dyn : Nat}
    (hm : MapState m ram res dyn) :
    fdt.discovery.add_ram_children m t.structure t.strings root ⦃ r m' =>
      Agrees (fun _ ram' => MapState m' ram' res dyn) errorOf r
        ((T.nodes.filter (·.isChildOf R)).foldlM ramOfChild ram) ⦄ := by
  obtain ⟨p, hp, rfl, hat⟩ := ht.of_nodeRepr hR
  unfold fdt.discovery.add_ram_children
  exact add_ram_children_loop_spec hu ht hp hat _ m _ 0#usize MAX_TOKENS.toNat [] ram start_repr.1
    (Nat.le_refl _) (Nat.zero_le _) (by rw [start_repr.2]; simpa using ht.walk) hm (by simp)

/-! ## Reserved regions -/

/-- The bytes of the name `no-map` that the code writes. -/
theorem discovery_bytes_no_map :
    bytesOf (Array.to_slice (Array.make 6#usize [110#u8, 111#u8, 45#u8, 109#u8, 97#u8, 112#u8])) =
      "no-map".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- The bytes of the name `reusable` that the code writes. -/
theorem discovery_bytes_reusable :
    bytesOf (Array.to_slice (Array.make 8#usize [114#u8, 101#u8, 117#u8, 115#u8, 97#u8, 98#u8,
      108#u8, 101#u8])) = "reusable".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- The bytes of the name `size` that the code writes. -/
theorem discovery_bytes_size :
    bytesOf (Array.to_slice (Array.make 4#usize [115#u8, 105#u8, 122#u8, 101#u8])) =
      "size".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- `reserved_of_child(map, structure, strings, node)`: `reservedOfChild` of the
reserved regions and the number of dynamic reservations of the map, which
leaves room for one more. -/
theorem reserved_of_child_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) {m : fdt.MemoryMap} {ram : List Span}
    {acc : List ReservedRegion × Nat} (hm : MapState m ram acc.1 acc.2)
    (hdyn : acc.2 + 1 < 2 ^ 64) :
    fdt.discovery.reserved_of_child m t.structure t.strings a ⦃ r m' =>
      Agrees (fun _ acc' => MapState m' ram acc'.1 acc'.2) errorOf r (reservedOfChild acc N) ⦄ := by
  unfold fdt.discovery.reserved_of_child
  rw [reservedOfChild_eq]
  step with enabled_at_spec hu h as ⟨r, r_post⟩
  refine try_state_spec r_post (fun e => from_residual_state_spec e m) fun v en hv _ => ?_
  subst hv
  cases v <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
  · exact spec_of_eq rfl hm
  simp only [lift, bind_ok]
  step with flag_at_spec hu h _ "no-map" discovery_bytes_no_map as ⟨r1, r1_post⟩
  refine try_state_spec r1_post (fun e => from_residual_state_spec e m) fun v1 noMap hv1 _ => ?_
  subst hv1
  step with flag_at_spec hu h _ "reusable" discovery_bytes_reusable as ⟨r2, r2_post⟩
  refine try_state_spec r2_post (fun e => from_residual_state_spec e m) fun v2 reusable hv2 _ => ?_
  subst hv2
  cases v1 <;> cases v2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false,
    Bool.and_true]
  case true.true => exact spec_of_eq rfl rfl
  all_goals
    step with has_property_spec hu h _ "reg" bytes_reg as ⟨b, b_post⟩
    rcases hreg : N.property "reg" with _ | v
    · rw [hreg] at b_post
      simp only [b_post, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      step with has_property_spec hu h _ "size" discovery_bytes_size as ⟨b1, b1_post⟩
      rcases hsize : N.property "size" with _ | w
      · rw [hsize] at b1_post
        simp only [b1_post, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, spec_ok]
        rfl
      · rw [hsize] at b1_post
        simp only [b1_post, Option.isSome_some, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hm
        step as ⟨i, i_post⟩
        exact ⟨h1, h2, h3, h4, by rw [i_post, h5]⟩
    · rw [hreg] at b_post
      simp only [b_post, Option.isSome_some, ↓reduceIte]
      step with reg_at_spec hu h as ⟨r3, r3_post⟩
      refine try_state_spec r3_post (fun e => from_residual_state_spec e m) fun g R hg _ => ?_
      obtain ⟨g1, g2, hR⟩ := hg
      simp only
      step as ⟨s3, s3_post⟩
      rw [← bytesOf_of_slice s3_post] at hR
      refine spec_mono (add_reserved_entries_spec hm s3 _ _ _ _ hR) ?_
      rintro ⟨r4, m4⟩ h4
      simp only [uncurry'_pair] at h4 ⊢
      exact agrees_bind_ok h4 fun _ _ h => h

/-- The loop of `add_reserved_children`: from a walker at the node of index
`count`, after at most `count` dynamic reservations, `reservedOfChild` of each
child of `/reserved-memory` from there on. -/
theorem add_reserved_children_loop_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {p : Nat} (hp : p < T.records.size) {parent : fdt.NodeAt}
    (hpar : AtRepr parent (L[p]'(ht.length ▸ hp))) {ram : List Span}
    (E : Except Krepi.Spec.Fdt.Error (List ReservedRegion × Nat)) (m : fdt.MemoryMap)
    (w : fdt.Walker) (count : Usize) (f : Nat) (st : List Nat) (acc : List ReservedRegion × Nat)
    (hw : WalkerRepr w st) (hf : f ≤ MAX_TOKENS.toNat) (hc : count.val ≤ L.length)
    (hL : nodesFrom (bytesOf t.structure) (bytesOf t.strings) f w.cursor.val st =
      some (L.drop count.val))
    (hm : MapState m ram acc.1 acc.2) (hd : acc.2 ≤ count.val)
    (hE : ((T.nodes.drop count.val).filter (·.isChildOf ⟨T, ⟨p, hp⟩⟩)).foldlM reservedOfChild acc =
      E) :
    fdt.discovery.add_reserved_children_loop m t.structure t.strings parent w count ⦃ r m' =>
      Agrees (fun _ acc' => MapState m' ram acc'.1 acc'.2) errorOf r E ⦄ := by
  have hlen := ht.length
  have hmax : L.length < MAX_TOKENS.toNat := (nodesFrom_sorted ht.walk).2.2
  rw [show MAX_TOKENS.toNat = 65536 from rfl] at hmax
  unfold fdt.discovery.add_reserved_children_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryMap × fdt.Walker × Usize) => L.length - x.2.2.val)
    (inv := fun (x : fdt.MemoryMap × fdt.Walker × Usize) => ∃ f st acc,
      WalkerRepr x.2.1 st ∧ f ≤ MAX_TOKENS.toNat ∧ x.2.2.val ≤ L.length ∧
      nodesFrom (bytesOf t.structure) (bytesOf t.strings) f x.2.1.cursor.val st =
        some (L.drop x.2.2.val) ∧ MapState x.1 ram acc.1 acc.2 ∧ acc.2 ≤ x.2.2.val ∧
      ((T.nodes.drop x.2.2.val).filter (·.isChildOf ⟨T, ⟨p, hp⟩⟩)).foldlM reservedOfChild acc = E)
  · rintro ⟨m, w, count⟩ ⟨f, st, acc, hw, hf, hc, hL, hm, hd, hE⟩
    simp only at hw hc hL hm hd hE
    unfold fdt.discovery.add_reserved_children_loop.body
    step
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post
    refine ite_spec_pos (by scalar_tac) ?_
    rcases Nat.lt_or_ge count.val L.length with hlt | hge
    · have hk : count.val < T.records.size := by omega
      rw [List.drop_eq_getElem_cons hlt] at hL
      have hdrop : T.nodes.drop count.val =
          ⟨T, ⟨count.val, hk⟩⟩ :: T.nodes.drop (count.val + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [nodes_length]; exact hk), nodes_getElem]
      rw [hdrop] at hE
      step with node_step_spec t.structure (bytesOf t.strings) w f st _ ht.size hw hf hL
      obtain ⟨⟨f', st', hf', hw', hL'⟩, a, ha, hat⟩ := next_post
      dsimp only at ha hL' hw'
      subst ha
      simp only
      step
      have hchild := ht.child_iff hk hp hat hpar
      have hN := (ht.nodeRepr_iff a count.val hk).2 hat
      by_cases hb : b = true
      · refine ite_spec_pos hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = true := by
          rw [← hchild, ← b_post]; exact hb
        simp only [List.filter_cons, hc1, ↓reduceIte, List.foldlM_cons] at hE
        step with reserved_of_child_spec hu hN hm (by omega) as ⟨r1, m1, hr1⟩
        cases r1 with
        | Err e =>
          have he := agrees_err_iff.mp hr1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with from_residual_spec e as ⟨r2, hr2⟩
          rw [hr2, ← hE, he]
          rfl
        | Ok u =>
          obtain ⟨acc1, hacc1, hm1⟩ := agrees_ok_iff.mp hr1
          have hd1 := reservedOfChild_snd hacc1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step as ⟨count1, count1_post⟩
          refine ⟨⟨f', st', acc1, hw', hf', by scalar_tac, by simpa [count1_post] using hL', hm1,
            by rw [count1_post]; omega, ?_⟩, by scalar_tac⟩
          rw [count1_post, ← hE, hacc1]; rfl
      · refine ite_spec_neg hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = false := by
          rw [← hchild, ← b_post]; simpa using hb
        simp only [List.filter_cons, hc1, Bool.false_eq_true, ↓reduceIte] at hE
        step as ⟨count1, count1_post⟩
        exact ⟨⟨f', st', acc, hw', hf', by scalar_tac, by simpa [count1_post] using hL', hm,
          by rw [count1_post]; omega, by rw [count1_post]; exact hE⟩, by scalar_tac⟩
    · rw [List.drop_of_length_le hge] at hL
      step with node_step_spec t.structure (bytesOf t.strings) w f st [] ht.size hw hf hL
      obtain ⟨-, hnone, -⟩ := next_post
      dsimp only at hnone
      subst hnone
      simp only [spec_ok]
      rw [List.drop_of_length_le (by rw [nodes_length]; omega), List.filter_nil,
        List.foldlM_nil] at hE
      rw [← hE]
      exact hm
  · exact ⟨f, st, acc, hw, hf, hc, hL, hm, hd, hE⟩

/-- `add_reserved_children(map, structure, strings, parent)`: `reservedOfChild`
of each child of the node in tree order, from no dynamic reservation. -/
theorem add_reserved_children_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {parent : fdt.NodeAt} {P : Node} (hP : NodeRepr ⟨t, parent⟩ P)
    {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    (hm : MapState m ram res 0) :
    fdt.discovery.add_reserved_children m t.structure t.strings parent ⦃ r m' =>
      Agrees (fun _ acc' => MapState m' ram acc'.1 acc'.2) errorOf r
        ((T.nodes.filter (·.isChildOf P)).foldlM reservedOfChild (res, 0)) ⦄ := by
  obtain ⟨p, hp, rfl, hat⟩ := ht.of_nodeRepr hP
  unfold fdt.discovery.add_reserved_children
  exact add_reserved_children_loop_spec hu ht hp hat _ m _ 0#usize MAX_TOKENS.toNat [] (res, 0)
    start_repr.1 (Nat.le_refl _) (Nat.zero_le _) (by rw [start_repr.2]; simpa using ht.walk) hm
    (Nat.zero_le _) (by simp)

/-- `reserved_memory_binding(structure, strings, parent, root)`:
`reservedMemoryBinding`. -/
theorem reserved_memory_binding_spec (hu : Usize64) {t : fdt.Fdt} {parent root : fdt.NodeAt}
    {P R : Node} (hP : NodeRepr ⟨t, parent⟩ P) (hR : NodeRepr ⟨t, root⟩ R) :
    fdt.discovery.reserved_memory_binding t.structure t.strings parent root ⦃ r =>
      Agrees (fun _ _ => True) errorOf r (reservedMemoryBinding P R) ⦄ := by
  unfold fdt.discovery.reserved_memory_binding
  rw [reservedMemoryBinding_eq]
  simp only [lift, bind_ok]
  step with has_property_spec hu hP _ "#address-cells" bytes_address_cells as ⟨b, b_post⟩
  rcases ha : P.property "#address-cells" with _ | va
  · rw [ha] at b_post
    simp only [b_post, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isNone_none,
      Bool.true_or, spec_ok]
    rfl
  rw [ha] at b_post
  simp only [b_post, Option.isSome_some, ↓reduceIte, Option.isNone_some, Bool.false_or]
  step with has_property_spec hu hP _ "#size-cells" bytes_size_cells as ⟨b1, b1_post⟩
  rcases hs : P.property "#size-cells" with _ | vs
  · rw [hs] at b1_post
    simp only [b1_post, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isNone_none,
      spec_ok]
    rfl
  rw [hs] at b1_post
  simp only [b1_post, Option.isSome_some, ↓reduceIte, Option.isNone_some, Bool.false_eq_true]
  step with address_cells_at_spec hu hP as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun v pa hv _ => ?_
  step with address_cells_at_spec hu hR as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun v1 ra hv1 _ => ?_
  subst hv hv1
  by_cases hne : v = v1
  · subst hne
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    step with size_cells_at_spec hu hP as ⟨r2, r2_post⟩
    refine try_spec r2_post (fun e => from_residual_spec e) fun v2 ps hv2 _ => ?_
    step with size_cells_at_spec hu hR as ⟨r3, r3_post⟩
    refine try_spec r3_post (fun e => from_residual_spec e) fun v3 rs hv3 _ => ?_
    subst hv2 hv3
    by_cases hne' : v2 = v3
    · subst hne'
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, not_true_eq_false]
      step with value_at_spec hu hP _ "ranges" bytes_ranges as ⟨o, ho⟩
      rcases o with _ | ⟨st, en⟩ <;> rcases hv : P.property "ranges" with _ | w <;> rw [hv] at ho
      · simp only [spec_ok]; rfl
      · exact ho.elim
      · exact ho.elim
      · obtain ⟨h1, h2, h3⟩ := ho
        dsimp only at h1 h2 h3
        have hsz : w.size = en.val - st.val := by
          rw [← h3, ByteArray.size_extract, bytesOf_size, Nat.min_eq_left h2]
        simp only [uncurry_apply_pair]
        by_cases he : st = en
        · subst he
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, spec_ok]
          have : w.size = 0 := by rw [hsz]; omega
          simp only [this, not_true_eq_false, ↓reduceIte]
          trivial
        · have hb : (st != en) = true := bne_iff_ne.2 he
          simp only [hb, ↓reduceIte, spec_ok]
          have : w.size ≠ 0 := by
            rw [hsz]; intro h0; exact he (UScalar.eq_of_val_eq (by omega))
          simp only [this, not_false_eq_true, ↓reduceIte]
          rfl
    · have hb : (v2 != v3) = true := bne_iff_ne.2 hne'
      have hw : word32 v2 ≠ word32 v3 := fun h => hne' (UScalar.eq_of_val_eq (by
        have := congrArg UInt32.toNat h; simpa using this))
      simp only [hb, ↓reduceIte, spec_ok, hw, not_false_eq_true]
      rfl
  · have hb : (v != v1) = true := bne_iff_ne.2 hne
    have hw : word32 v ≠ word32 v1 := fun h => hne (UScalar.eq_of_val_eq (by
      have := congrArg UInt32.toNat h; simpa using this))
    simp only [hb, ↓reduceIte, spec_ok, hw, ne_eq, not_false_eq_true]
    rfl

/-- The bytes of the path that `add_reserved_memory` looks up. -/
theorem discovery_path_reserved_memory :
    (Array.to_slice (Array.make 16#usize [47#u8, 114#u8, 101#u8, 115#u8, 101#u8, 114#u8, 118#u8,
      101#u8, 100#u8, 45#u8, 109#u8, 101#u8, 109#u8, 111#u8, 114#u8, 121#u8])).val.map byte =
      utf8Bytes "/reserved-memory".toList := by
  rfl

/-- `add_reserved_memory(map, structure, strings, root)`: `Fdt.reservedMemory`
after the reserved regions of the map, from no dynamic reservation. -/
theorem add_reserved_memory_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {root : fdt.NodeAt} {R : Node} (hR : NodeRepr ⟨t, root⟩ R)
    {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    (hm : MapState m ram res 0) :
    fdt.discovery.add_reserved_memory m t.structure t.strings root ⦃ r m' =>
      Agrees (fun _ p => MapState m' ram p.1 p.2) errorOf r (T.reservedMemory R res) ⦄ := by
  unfold fdt.discovery.add_reserved_memory
  rw [reservedMemory_eq, findNode_reserved_memory]
  simp only [lift, bind_ok]
  step with find_path_spec ht (Array.to_slice (Array.make 16#usize [47#u8, 114#u8, 101#u8, 115#u8,
    101#u8, 114#u8, 118#u8, 101#u8, 100#u8, 45#u8, 109#u8, 101#u8, 109#u8, 111#u8, 114#u8, 121#u8]))
    (by simp [usize_max hu]) (by simp) as ⟨r, r_post⟩
  simp only [Array.length_to_slice, show ¬ (16#usize : Usize).val = 1 from by decide,
    ↓reduceIte, discovery_path_reserved_memory] at r_post
  refine try_state_spec r_post (fun e => from_residual_state_spec e m) fun o oP ho _ => ?_
  rcases o with _ | parent <;> rcases oP with _ | P
  · exact spec_of_eq rfl hm
  · exact ho.elim
  · exact ho.elim
  · simp only
    step with reserved_memory_binding_spec hu ho hR as ⟨r1, r1_post⟩
    refine try_state_spec r1_post (fun e => from_residual_state_spec e m) fun _ _ _ _ => ?_
    step with enabled_at_spec hu ho as ⟨r2, r2_post⟩
    refine try_state_spec r2_post (fun e => from_residual_state_spec e m) fun v en hv _ => ?_
    subst hv
    cases v <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
    · exact spec_of_eq rfl hm
    · exact add_reserved_children_spec hu ht ho hm

/-! ## The discovery -/

/-- `NO_MEMORY`: no range, no region, no dynamic reservation. -/
theorem no_memory_state : MapState fdt.discovery.NO_MEMORY [] [] 0 := by
  unfold fdt.discovery.NO_MEMORY
  simp [MapState, MAX_MEMORY_REGIONS, MAX_RESERVED_REGIONS]

/-- A memory map of the code at the end of the discovery stands for the memory
map of its lists and number. -/
theorem mapState_repr {m : fdt.MemoryMap} {ram : List Span} {res : List ReservedRegion}
    {dyn : Nat} (hm : MapState m ram res dyn) :
    MemoryMapRepr m ⟨ram, res, UInt64.ofNat dyn⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  refine ⟨h1, h2, ?_⟩
  rw [h3, h4, word64, h5]

/-- `Fdt::discover_memory()`: the statement `FdtDiscoverMemory`, the memory map
of `Fdt.discoverMemory` or its error, for a tree that stands for a tree. -/
@[step] theorem fdt_discover_memory_spec (hu : Usize64) (t : fdt.Fdt) (T : Fdt)
    (h : FdtRepr t T) :
    fdt.discovery.Fdt.discover_memory t ⦃ r =>
      Agrees MemoryMapRepr errorOf r T.discoverMemory ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h
  obtain ⟨hl, hr⟩ := fdtRepr_reservations h
  unfold fdt.discovery.Fdt.discover_memory
  step with add_map_entries_spec no_memory_state t.reservations T.reservations hl hr
    as ⟨r, m, hrm⟩
  rcases hroot : T.root with _ | R
  · rw [discoverMemory_none hroot]
    refine try_spec hrm (fun e => from_residual_spec e) fun _ mapped hmapped _ => ?_
    step with first_node_spec ht as ⟨o, ho⟩
    rw [hroot] at ho
    rcases o with _ | root
    · exact spec_of_eq rfl rfl
    · exact ho.elim
  · rw [discoverMemory_some hroot]
    refine try_spec hrm (fun e => from_residual_spec e) fun _ mapped hmapped _ => ?_
    step with first_node_spec ht as ⟨o, ho⟩
    rw [hroot] at ho
    rcases o with _ | root
    · exact ho.elim
    simp only
    step with add_ram_children_spec hu ht ho hmapped as ⟨r1, m1, hr1⟩
    refine try_spec hr1 (fun e => from_residual_spec e) fun _ ram hram _ => ?_
    have hlen := mapState_ram_length hram
    by_cases hz : m1.ram_count = 0#usize
    · have : ram.isEmpty = true := by
        rw [List.isEmpty_iff, ← List.length_eq_zero_iff, hlen, hz]; rfl
      simp only [hz, ↓reduceIte, this, spec_ok]
      rfl
    · have : ram.isEmpty = false := by
        rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff, hlen]
        intro h0; exact hz (UScalar.eq_of_val_eq h0)
      simp only [hz, ↓reduceIte, this, Bool.false_eq_true]
      step with add_reserved_memory_spec hu ht ho hram as ⟨r2, m2, hr2⟩
      refine try_spec hr2 (fun e => from_residual_spec e) fun _ p hp _ => ?_
      obtain ⟨res', dyn'⟩ := p
      exact spec_of_eq rfl (mapState_repr hp)

end Krepi.Proofs.Fdt.Refinement

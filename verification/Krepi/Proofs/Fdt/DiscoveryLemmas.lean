module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.Translate

/-!
# Device tree: lemmas about the discoveries

Lemmas about `Fdt::discover_memory`, `Fdt::discover_boot_memory` and
`Fdt::discover_cpus` of the specification of the `fdt` component: what a
success tells about each of their steps, for the proofs of the statements
about the memory map, the boot memory and the CPU nodes.

- The RAM ranges: `RamOk` (at most `MAX_MEMORY_REGIONS`, nonempty, no two
  touching), kept by each range (`addRam_fold`) and each child of the root
  (`ramOfChild_ok`, `ramOfChild_fold`); the ranges are those of the enabled
  memory nodes in tree order (`enabledB`, `regEntries`), and with the root
  of the lookup of `/` they are `Fdt.memoryNodeSpans` (`ram_spans`).
- The reserved regions: `ReservedOk` (at most `MAX_RESERVED_REGIONS`,
  nonempty, not both `no-map` and `reusable`), kept by the entries of the
  reservation map (`pushReserved_fold`) and by the children of
  `/reserved-memory` (`addReservedSpan_fold`, `reservedOfChild_ok`,
  `reservedOfChild_fold`, `reservedMemory_ok`), whose dynamic reservations
  are at most the nodes of the tree (`nodes_length`).
- The discoveries: `discoverMemory_ok` (all of the above of a memory map),
  `checkedAdd_fold` (the sum of the RAM ranges), `discoverBootMemory_ok` (the
  memory map of a boot memory is that of `Fdt::discover_memory`, and the boot
  memory is consistent and holds the limit and the alignment of its
  hand-over profile).
- The CPU nodes: `IsCpu`, `cpuOfChild_ok` and `cpuOfChild_fold` (no two CPU
  nodes of an accepted `/cpus` have one `reg`), `pairwise_mem_ne` and
  `cpus_distinct_regs`.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt

/-- The RAM ranges of a memory map so far: at most `MAX_MEMORY_REGIONS`, each
nonempty, no two touching. -/
def RamOk (ram : List Span) : Prop :=
  ram.length ≤ MAX_MEMORY_REGIONS.toNat ∧ (∀ s ∈ ram, s.Nonempty) ∧
    ram.Pairwise (fun a b => a.touches b = false)

/-- The reserved regions of a memory map so far. -/
def ReservedOk (l : List ReservedRegion) : Prop :=
  l.length ≤ MAX_RESERVED_REGIONS.toNat ∧
    ∀ r ∈ l, r.span.Nonempty ∧ (r.noMap && r.reusable) = false

/-- The entries of the `reg` of a node lie within 64 bits. -/
theorem reg_valid {n : Node} {r : Reg} (h : n.reg = .ok r) : ∀ s ∈ r.entries, s.Valid := by
  unfold Node.reg at h
  split at h
  · split at h
    · obtain ⟨ac, -, h⟩ := except_bind_ok.1 h
      obtain ⟨sc, -, h⟩ := except_bind_ok.1 h
      exact fun s hs => ((Translate.regNewWellFormed _ _ _ _ h).2 s hs).1
    · exact absurd h (except_throw_ne _ _)
  · exact absurd h (except_throw_ne _ _)

/-- RAM ranges added in order: appended after the ranges so far, keeping
`RamOk`. -/
theorem addRam_fold : ∀ (l acc res : List Span), l.foldlM addRam acc = .ok res →
    (∀ s ∈ l, s.Valid) → RamOk acc → res = acc ++ l ∧ RamOk res
  | [], acc, res, h, _, hacc => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    simp [hacc]
  | s :: l, acc, res, h, hv, hacc => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    unfold addRam at h1
    split at h1
    · cases h1
    · rename_i hs
      split at h1
      · cases h1
      · rename_i hany
        split at h1
        · cases h1
        · rename_i hlen
          cases h1
          have hacc' : RamOk (acc ++ [s]) := by
            refine ⟨?_, ?_, ?_⟩
            · simp only [List.length_append, List.length_singleton]
              omega
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hacc.2.1 x hx
              · rw [List.mem_singleton] at hx
                subst hx
                exact ⟨hs, hv _ List.mem_cons_self⟩
            · rw [List.pairwise_append]
              refine ⟨hacc.2.2, List.pairwise_singleton _ _, ?_⟩
              intro a ha b hb
              rw [List.mem_singleton] at hb
              subst hb
              simp only [Bool.not_eq_true, List.any_eq_true, not_exists, not_and] at hany
              simpa using hany a ha
          obtain ⟨h1, h2⟩ := addRam_fold l _ res h
            (fun x hx => hv x (List.mem_cons_of_mem _ hx))
            hacc'
          exact ⟨by rw [h1]; simp, h2⟩

/-- Whether a node is enabled, a failed `status` counting as disabled. -/
def enabledB (n : Node) : Bool :=
  match n.enabled with
  | .ok b => b
  | .error _ => false

/-- The entries of the `reg` of a node, none when it fails. -/
def regEntries (n : Node) : List Span :=
  match n.reg with
  | .ok r => r.entries
  | .error _ => []

/-- One child of the root adds nothing unless it has a memory name and is
enabled, and then the ranges of its `reg`. -/
theorem ramOfChild_ok {ram res : List Span} {n : Node} (h : ramOfChild ram n = .ok res) :
    ((isMemoryName n.name && enabledB n) = false ∧ res = ram) ∨
    (isMemoryName n.name = true ∧ n.enabled = .ok true ∧
      ∃ r, n.reg = .ok r ∧ r.entries.foldlM addRam ram = .ok res) := by
  unfold ramOfChild at h
  obtain ⟨dt, hdt, h⟩ := except_bind_ok.1 h
  dsimp only at h
  split at h
  · rename_i hc
    left
    refine ⟨?_, (except_pure_ok.1 h).symm⟩
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hc
    simp [hc.1]
  · rename_i hc
    obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
    split at h
    · rename_i hb'
      left
      refine ⟨?_, (except_pure_ok.1 h).symm⟩
      simp only [Bool.not_eq_true'] at hb'
      subst hb'
      simp [enabledB, hb]
    · rename_i hb'
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hb'
      subst hb'
      obtain ⟨hc2, h⟩ := except_jp_ok h
      obtain ⟨r, hr, h⟩ := except_bind_ok.1 h
      right
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at hc2
      exact ⟨hc2.1, hb, r, hr, h⟩

/-- The children of the root add the ranges of the `reg` of each enabled node
with a memory name, in order, keeping `RamOk`. -/
theorem ramOfChild_fold : ∀ (l : List Node) (acc res : List Span),
    l.foldlM ramOfChild acc = .ok res → RamOk acc →
    res = acc ++ (l.filter fun n => isMemoryName n.name && enabledB n).flatMap regEntries ∧
      RamOk res
  | [], acc, res, h, hacc => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    simp [hacc]
  | n :: l, acc, res, h, hacc => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    rcases ramOfChild_ok h1 with ⟨hf, he⟩ | ⟨hn, he, r, hr, hf⟩
    · rw [he] at h
      obtain ⟨h2, h3⟩ := ramOfChild_fold l _ res h hacc
      refine ⟨?_, h3⟩
      rw [h2, List.filter_cons, hf]
      rfl
    · obtain ⟨ha1, ha2⟩ := addRam_fold _ _ _ hf (reg_valid hr) hacc
      obtain ⟨h2, h3⟩ := ramOfChild_fold l _ res h ha2
      refine ⟨?_, h3⟩
      have hb : (isMemoryName n.name && enabledB n) = true := by simp [hn, enabledB, he]
      rw [h2, ha1, List.filter_cons, hb]
      simp [regEntries, hr]

/-- The entries of the reservation map as reserved regions keep `ReservedOk`.
-/
theorem pushReserved_fold : ∀ (l : List Span) (acc res : List ReservedRegion),
    l.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) acc = .ok res →
    (∀ s ∈ l, s.Nonempty) → ReservedOk acc → ReservedOk res
  | [], acc, res, h, _, hacc => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact hacc
  | s :: l, acc, res, h, hs, hacc => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    unfold pushReserved at h1
    split at h1
    · cases h1
    · rename_i hlen
      cases h1
      refine pushReserved_fold l _ res h (fun x hx => hs x (List.mem_cons_of_mem _ hx)) ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact hacc.2 r hr
        · rw [List.mem_singleton] at hr
          subst hr
          exact ⟨hs s List.mem_cons_self, rfl⟩

/-- The spans of a child of `/reserved-memory` without both flags keep
`ReservedOk`. -/
theorem addReservedSpan_fold {noMap reusable : Bool} (hf : (noMap && reusable) = false) :
    ∀ (l : List Span) (acc res : List ReservedRegion),
    l.foldlM (addReservedSpan noMap reusable) acc = .ok res →
    (∀ s ∈ l, s.Valid) → ReservedOk acc → ReservedOk res
  | [], acc, res, h, _, hacc => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact hacc
  | s :: l, acc, res, h, hs, hacc => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    unfold addReservedSpan pushReserved at h1
    split at h1
    · cases h1
    · rename_i hsz
      split at h1
      · cases h1
      · rename_i hlen
        cases h1
        refine addReservedSpan_fold hf l _ res h (fun x hx => hs x (List.mem_cons_of_mem _ hx))
          ⟨?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact hacc.2 r hr
          · rw [List.mem_singleton] at hr
            subst hr
            exact ⟨⟨hsz, hs s List.mem_cons_self⟩, hf⟩

/-- One child of `/reserved-memory` keeps `ReservedOk` and counts at most one
dynamic reservation. -/
theorem reservedOfChild_ok {acc res : List ReservedRegion × Nat} {n : Node}
    (h : reservedOfChild acc n = .ok res) :
    (ReservedOk acc.1 → ReservedOk res.1) ∧ res.2 ≤ acc.2 + 1 := by
  unfold reservedOfChild at h
  obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
  split at h
  · cases except_pure_ok.1 h
    exact ⟨id, Nat.le_succ _⟩
  · obtain ⟨noMap, -, h⟩ := except_bind_ok.1 h
    obtain ⟨reusable, -, h⟩ := except_bind_ok.1 h
    obtain ⟨hf, h⟩ := except_jp_ok h
    split at h
    · exact absurd h (except_throw_ne _ _)
    · cases except_pure_ok.1 h
      exact ⟨id, Nat.le_refl _⟩
    · obtain ⟨r, hr, h⟩ := except_bind_ok.1 h
      obtain ⟨reserved, hres, h⟩ := except_bind_ok.1 h
      cases except_pure_ok.1 h
      simp only [Bool.not_eq_true] at hf
      exact ⟨fun hacc => addReservedSpan_fold hf _ _ _ hres (reg_valid hr) hacc,
        Nat.le_succ _⟩

/-- The children of `/reserved-memory` keep `ReservedOk` and count at most one
dynamic reservation each. -/
theorem reservedOfChild_fold : ∀ (l : List Node) (acc res : List ReservedRegion × Nat),
    l.foldlM reservedOfChild acc = .ok res →
    (ReservedOk acc.1 → ReservedOk res.1) ∧ res.2 ≤ acc.2 + l.length
  | [], acc, res, h => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact ⟨id, Nat.le_refl _⟩
  | n :: l, acc, res, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    obtain ⟨h1a, h1b⟩ := reservedOfChild_ok h1
    obtain ⟨h2a, h2b⟩ := reservedOfChild_fold l _ res h
    refine ⟨fun hacc => h2a (h1a hacc), ?_⟩
    simp only [List.length_cons]
    omega

/-- A tree has as many nodes as records. -/
theorem nodes_length (t : Fdt) : t.nodes.length = t.records.size := by
  simp [Fdt.nodes]

/-- The reserved regions of `/reserved-memory` keep `ReservedOk`, with at most
as many dynamic reservations as nodes. -/
theorem reservedMemory_ok {t : Fdt} {root : Node} {mapped : List ReservedRegion}
    {res : List ReservedRegion × Nat} (h : t.reservedMemory root mapped = .ok res) :
    (ReservedOk mapped → ReservedOk res.1) ∧ res.2 ≤ t.records.size := by
  unfold Fdt.reservedMemory at h
  obtain ⟨found, -, h⟩ := except_bind_ok.1 h
  split at h
  · cases except_pure_ok.1 h
    exact ⟨id, Nat.zero_le _⟩
  · obtain ⟨u, -, h⟩ := except_bind_ok.1 h
    obtain ⟨b, -, h⟩ := except_bind_ok.1 h
    split at h
    · cases except_pure_ok.1 h
      exact ⟨id, Nat.zero_le _⟩
    · obtain ⟨h1, h2⟩ := reservedOfChild_fold _ _ _ h
      refine ⟨h1, Nat.le_trans h2 ?_⟩
      show 0 + _ ≤ _
      rw [Nat.zero_add, ← nodes_length]
      exact List.length_filter_le _ _

/-- A memory map of `Fdt::discover_memory`: the root of the lookup of `/`, the
RAM ranges of its enabled memory children in order, `RamOk` and not empty,
the reserved regions `ReservedOk` when the reservation map is, and a number
of dynamic reservations at most the number of nodes. -/
theorem discoverMemory_ok {t : Fdt} {m : MemoryMap} (h : t.discoverMemory = .ok m) :
    ∃ root, t.findNode "/" = .ok (some root) ∧
      m.ram = ((t.nodes.filter (·.isChildOf root)).filter
        fun n => isMemoryName n.name && enabledB n).flatMap regEntries ∧
      RamOk m.ram ∧ m.ram ≠ [] ∧
      ((∀ s ∈ t.reservations, s.Nonempty) → ReservedOk m.reserved) ∧
      ∃ d, d ≤ t.records.size ∧ m.dynamic = UInt64.ofNat d := by
  unfold Fdt.discoverMemory at h
  obtain ⟨mapped, hmapped, h⟩ := except_bind_ok.1 h
  obtain ⟨found, hfound, h⟩ := except_bind_ok.1 h
  split at h
  · rename_i root
    obtain ⟨ram, hram, h⟩ := except_bind_ok.1 h
    obtain ⟨hne, h⟩ := except_jp_ok h
    obtain ⟨⟨reserved, dyn⟩, hrm, h⟩ := except_bind_ok.1 h
    cases except_pure_ok.1 h
    have hm := fun hres => pushReserved_fold _ _ _ hmapped hres ⟨Nat.zero_le _, by simp⟩
    obtain ⟨hr1, hr2⟩ := ramOfChild_fold _ _ _ hram
      ⟨Nat.zero_le _, by simp, List.Pairwise.nil⟩
    obtain ⟨hv1, hv2⟩ := reservedMemory_ok hrm
    exact ⟨root, hfound, by simpa using hr1, hr2, by simpa using hne, fun hres => hv1 (hm hres),
      dyn, hv2, rfl⟩
  · exact absurd h (except_throw_ne _ _)

/-- A sum of sizes with `checkedAdd` is the exact sum and fits in 64 bits. -/
theorem checkedAdd_fold : ∀ (l : List Span) (init res : Nat),
    l.foldlM (fun sum s => checkedAdd sum s.size.toNat) init = .ok res → init < 2 ^ 64 →
    res = l.foldl (fun sum s => sum + s.size.toNat) init ∧ res < 2 ^ 64
  | [], init, res, h, hi => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact ⟨rfl, hi⟩
  | s :: l, init, res, h, _ => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    obtain ⟨hlt, he⟩ := checkedAdd_ok.1 h1
    subst he
    exact checkedAdd_fold l _ res h hlt

/-- A boot memory has the memory map of `Fdt::discover_memory`, is
consistent, and holds the size limit and the alignment of the hand-over
profile that it was given. -/
theorem discoverBootMemory_ok {t : Fdt} {handOver : HandOverProfile} {a : UInt64} {image : Span}
    {m : BootMemory} (h : t.discoverBootMemory handOver a image = .ok m) :
    t.discoverMemory = .ok m.memory ∧ m.Consistent ∧ m.maxBlobSize = handOver.maxBlobSize ∧
      m.alignmentLog2 = handOver.alignmentLog2 := by
  unfold Fdt.discoverBootMemory at h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨h2, h⟩ := except_jp_ok h
  obtain ⟨found, -, h⟩ := except_bind_ok.1 h
  split at h
  · obtain ⟨ac, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨sc, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    split at h
    · obtain ⟨u, -, h⟩ := except_bind_ok.1 h
      obtain ⟨dtb, hdtb, h⟩ := except_bind_ok.1 h
      obtain ⟨h3, h⟩ := except_jp_ok h
      obtain ⟨e, he, h⟩ := except_bind_ok.1 h
      obtain ⟨h4, h⟩ := except_jp_ok h
      obtain ⟨mem, hmem, h⟩ := except_bind_ok.1 h
      obtain ⟨h5, h⟩ := except_jp_ok h
      obtain ⟨h6, h⟩ := except_jp_ok h
      obtain ⟨rb, hrb, h⟩ := except_bind_ok.1 h
      cases except_pure_ok.1 h
      obtain ⟨hlt, hdtbeq⟩ := span_new_ok.1 hdtb
      subst hdtbeq
      obtain ⟨hrb1, hrb2⟩ := checkedAdd_fold _ _ _ hrb (by decide)
      refine ⟨hmem, ⟨hlt, ?_, ?_, ⟨h3, endAddr_ok he⟩, by simpa using h4,
        by simpa [BootMemory.ram] using h5, by simpa [BootMemory.ram] using h6, ?_⟩, rfl, rfl⟩
      · simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using h2
      · exact UInt64.not_lt.1 h1
      · show (UInt64.ofNat rb).toNat = _
        rw [UInt64.toNat_ofNat_of_lt' hrb2, hrb1]
        rfl
    · exact absurd h (except_throw_ne _ _)
  · exact absurd h (except_throw_ne _ _)

/-- The RAM ranges of `Fdt::discover_memory` are the spans of the enabled
memory nodes below the root, in tree order. -/
theorem ram_spans : ∀ (t : Fdt) (m : MemoryMap) (root : Node),
    t.discoverMemory = .ok m → t.findNode "/" = .ok (some root) →
      m.ram = t.memoryNodeSpans root := by
  intro t m root h hroot
  obtain ⟨root', hroot', hram, -⟩ := discoverMemory_ok h
  rw [hroot] at hroot'
  cases hroot'
  rw [hram]
  simp only [Fdt.memoryNodeSpans, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro n _
  simp only [enabledB]
  cases n.isChildOf root <;> cases isMemoryName n.name <;> cases n.enabled <;> simp

/-- A CPU node: its `device_type` is `cpu`. -/
def IsCpu (n : Node) : Prop := n.stringProperty "device_type" = .ok (some "cpu")

/-- One child of `/cpus` adds nothing when it is no CPU node, and otherwise the
new ID of its `reg`. -/
theorem cpuOfChild_ok {profile : CpuProfile} {cells : UInt32} {ids res : List UInt64} {n : Node}
    (h : cpuOfChild profile cells ids n = .ok res) :
    (¬ IsCpu n ∧ res = ids) ∨
    ∃ reg aff id, n.property "reg" = some reg ∧ cellsU64 reg cells = .ok aff ∧
      profile.idOf aff = some id ∧ id ∉ ids ∧ res = ids ++ [id] := by
  unfold cpuOfChild at h
  obtain ⟨dt, hdt, h⟩ := except_bind_ok.1 h
  split at h
  · left
    rename_i hc
    refine ⟨fun e => ?_, (except_pure_ok.1 h).symm⟩
    rw [IsCpu, hdt] at e
    cases e
    simp at hc
  · right
    obtain ⟨b, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨cp, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    split at h
    · rename_i reg hreg
      obtain ⟨aff, haff, h⟩ := except_bind_ok.1 h
      split at h
      · rename_i id hid
        obtain ⟨hcont, h⟩ := except_jp_ok h
        refine ⟨reg, aff, id, hreg, haff, hid, by simpa using hcont, ?_⟩
        dsimp only at h
        split at h
        · obtain ⟨_, -, h⟩ := except_bind_ok.1 h
          obtain ⟨-, h⟩ := except_jp_ok h
          exact (except_pure_ok.1 h).symm
        · exact (except_pure_ok.1 h).symm
      · exact absurd h (except_throw_ne _ _)
    · exact absurd h (except_throw_ne _ _)

/-- The children of an accepted `/cpus`: each CPU node has an ID that the IDs
before the list do not hold, and no two CPU nodes have one `reg`. -/
theorem cpuOfChild_fold (profile : CpuProfile) (cells : UInt32) :
    ∀ (l : List Node) (acc res : List UInt64),
    l.foldlM (cpuOfChild profile cells) acc = .ok res →
    (∀ y ∈ l, IsCpu y → ∃ reg aff id, y.property "reg" = some reg ∧
      cellsU64 reg cells = .ok aff ∧
      profile.idOf aff = some id ∧ id ∉ acc) ∧
    l.Pairwise (fun x y => IsCpu x → IsCpu y → x.property "reg" ≠ y.property "reg")
  | [], _, _, _ => ⟨by simp, List.Pairwise.nil⟩
  | x :: l, acc, res, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    obtain ⟨ih1, ih2⟩ := cpuOfChild_fold profile cells l acc' res h
    rcases cpuOfChild_ok h1 with ⟨hx, he⟩ | ⟨reg, aff, id, hreg, haff, hid, hnot, he⟩
    · subst he
      refine ⟨fun y hy hc => ?_, List.pairwise_cons.2 ⟨fun _ _ hc => absurd hc hx, ih2⟩⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hc hx
      · exact ih1 y hy hc
    · subst he
      refine ⟨fun y hy hc => ?_, List.pairwise_cons.2 ⟨fun y hy _ hcy e => ?_, ih2⟩⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨reg, aff, id, hreg, haff, hid, hnot⟩
        · obtain ⟨r, a, i, h1, h2, h3, h4⟩ := ih1 y hy hc
          exact ⟨r, a, i, h1, h2, h3, fun e => h4 (List.mem_append_left _ e)⟩
      · obtain ⟨r, a, i, h1, h2, h3, h4⟩ := ih1 y hy hcy
        rw [hreg, h1] at e
        cases e
        rw [haff] at h2
        cases h2
        rw [hid] at h3
        cases h3
        exact h4 (List.mem_append_right _ (List.mem_singleton_self _))

/-- Two distinct entries of a list whose pairs keep `R`, in some order. -/
theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha1 | ha1 <;> rcases List.mem_cons.1 hb with hb1 | hb1
    · exact absurd (ha1.trans hb1.symm) hab
    · exact Or.inl (ha1 ▸ h.1 _ hb1)
    · exact Or.inr (hb1 ▸ h.1 _ ha1)
    · exact pairwise_mem_ne h.2 ha1 hb1 hab

/-- No two CPU nodes of an accepted `/cpus` have one `reg`. -/
theorem cpus_distinct_regs :
    ∀ (t : Fdt) (profile : CpuProfile) (topology : CpuTopology) (cpus : Node),
    t.discoverCpus profile = .ok topology → t.findNode "/cpus" = .ok (some cpus) →
    ∀ n ∈ t.nodes, ∀ m ∈ t.nodes, n.isChildOf cpus = true → m.isChildOf cpus = true →
      n.stringProperty "device_type" = .ok (some "cpu") →
      m.stringProperty "device_type" = .ok (some "cpu") →
      n.index.val ≠ m.index.val → n.property "reg" ≠ m.property "reg" := by
  intro t profile topology cpus h hc n hn m hm hnc hmc hnd hmd hne
  unfold Fdt.discoverCpus at h
  rw [hc, except_ok_bind] at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨cells, _, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨ids, hids, -⟩ := except_bind_ok.1 h
  obtain ⟨-, hpw⟩ := cpuOfChild_fold profile cells _ _ _ hids
  have hnm : n ≠ m := fun e => hne (congrArg (fun x : Node => x.index.val) e)
  rcases pairwise_mem_ne hpw (List.mem_filter.2 ⟨hn, hnc⟩) (List.mem_filter.2 ⟨hm, hmc⟩)
    hnm with
    h1 | h1
  · exact h1 hnd hmd
  · exact fun e => h1 hmd hnd e.symm

end Krepi.Proofs.Fdt

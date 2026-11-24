module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PlanLemmas

/-!
# Device tree: lemmas about the selection of the boot memory

Lemmas about `BootMemory::find_available` of the specification of the
`fdt` component, for the proofs of the statements about it:

- `alignUp_ok`: the least aligned address at or above an address;
- `SearchAccepts`: the starts of candidates that the search of one RAM range
  accepts, with `cand_toNat` and `cand_size_ne` about the candidate at a
  start;
- the search of one range: `skip_not_accepted` (the next candidate skips no
  accepted start), `searchRange_some` (a span is the candidate at the least
  accepted start) and `searchRange_none` (none means that no start is
  accepted), neither of which needs the fuel to suffice;
- the search through the ranges: `searchRanges_some`, `searchRanges_none`;
- `findAvailable_ok`: the checks before the search;
- `accepts_of_fits` and `fits_of_accepts`: a span that fits a range
  (`BootMemory.Fits`) is the candidate at an accepted start at or above
  the first candidate of that range, and conversely.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- A success of `alignUp` is the least multiple of the alignment at or above
the address, below `2 ^ 64`. -/
theorem alignUp_ok {a al c : Nat} (hal : 0 < al) (h : alignUp a al = .ok c) :
    a ≤ c ∧ c % al = 0 ∧ c < 2 ^ 64 ∧ ∀ t, a ≤ t → t % al = 0 → c ≤ t := by
  unfold alignUp at h
  dsimp only at h
  split at h
  · rename_i hlt
    injection h with h
    subst h
    refine ⟨?_, Nat.mul_mod_left _ _, hlt, ?_⟩
    · have := @Nat.lt_div_mul_add (a + al - 1) al hal
      omega
    · intro t hat ht
      have h2 : t / al * al = t := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ht)
      have hq : (a + al - 1) / al < t / al + 1 := by
        rw [Nat.div_lt_iff_lt_mul hal, Nat.add_mul, Nat.one_mul]
        omega
      have := Nat.mul_le_mul_right al (Nat.le_of_lt_succ hq)
      omega
  · cases h

/-- The start `t` of a candidate of `size` bytes that the search of one range
with the end `bound` accepts: aligned, its end within 64 bits and `bound`,
and touching no exclusion. -/
def SearchAccepts (m : BootMemory) (size al bound t : Nat) : Prop :=
  t % al = 0 ∧ t + size < 2 ^ 64 ∧ t + size ≤ bound ∧
    ∀ x ∈ m.exclusions, x.touches ⟨UInt64.ofNat t, UInt64.ofNat size⟩ = false

/-- The start, size and end of a candidate within 64 bits. -/
theorem cand_toNat {t size : Nat} (h : t + size < 2 ^ 64) :
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).start.toNat = t ∧
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).size.toNat = size ∧
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).endNat = t + size := by
  have hu : UInt64.size = 2 ^ 64 := rfl
  have h1 : (UInt64.ofNat t).toNat = t := UInt64.toNat_ofNat_of_lt' (by omega)
  have h2 : (UInt64.ofNat size).toNat = size := UInt64.toNat_ofNat_of_lt' (by omega)
  exact ⟨h1, h2, by unfold Span.endNat; rw [h1, h2]⟩

/-- A candidate of a nonzero size within 64 bits is not empty. -/
theorem cand_size_ne {t size : Nat} (h : t + size < 2 ^ 64) (hs : 0 < size) :
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).size ≠ 0 := by
  intro h0
  have := (cand_toNat h).2.1
  rw [h0] at this
  simp at this
  omega

/-- After a candidate at `c` that touches exclusions, the next candidate lies
past `c`, and the search accepts no start from `c` up to it. -/
theorem skip_not_accepted {m : BootMemory} {size al bound c next : Nat} (hs : 0 < size)
    (hal : 0 < al) (hc : c + size < 2 ^ 64)
    (hne : (m.exclusions.filter
      (·.touches ⟨UInt64.ofNat c, UInt64.ofNat size⟩)).isEmpty = false)
    (hnext : alignUp ((m.exclusions.filter
      (·.touches ⟨UInt64.ofNat c, UInt64.ofNat size⟩)).foldl (fun e s => max e s.endNat) 0) al =
        .ok next) :
    c < next ∧ ∀ u, c ≤ u → u < next → ¬ SearchAccepts m size al bound u := by
  generalize htd :
    m.exclusions.filter (·.touches ⟨UInt64.ofNat c, UInt64.ofNat size⟩) = touched at hne hnext
  obtain ⟨-, hall, hone⟩ := foldl_max_spec Span.endNat touched 0
  generalize hEdef : touched.foldl (fun e s => max e s.endNat) 0 = E at hnext hall hone
  obtain ⟨hE, -, -, hmin⟩ := alignUp_ok hal hnext
  obtain ⟨y, hy⟩ : ∃ y, y ∈ touched := by
    cases h : touched with
    | nil => rw [h] at hne; simp at hne
    | cons y _ => exact ⟨y, List.mem_cons_self⟩
  have hyt := (List.mem_filter.1 (htd ▸ hy)).2
  obtain ⟨hcs, -, hce⟩ := cand_toNat hc
  rw [touches_iff, hcs, hce] at hyt
  have hyE := hall y hy
  refine ⟨by omega, ?_⟩
  intro u hcu hun hg
  obtain ⟨hgm, hglt, -, hgx⟩ := hg
  by_cases huE : u < E
  · rcases hone with h0 | ⟨x, hx, hxE⟩
    · omega
    · have hxt := (List.mem_filter.1 (htd ▸ hx)).2
      have hxm := (List.mem_filter.1 (htd ▸ hx)).1
      have := hgx x hxm
      rw [touches_iff, hcs, hce] at hxt
      obtain ⟨hus, -, hue⟩ := cand_toNat hglt
      have hxu : x.touches ⟨UInt64.ofNat u, UInt64.ofNat size⟩ = true := by
        rw [touches_iff, hus, hue]
        exact ⟨hxt.1, cand_size_ne hglt hs, by omega, by omega⟩
      rw [hxu] at this
      cases this
  · have := hmin u (by omega) hgm
    omega

/-- A search of one range that ends with none accepts no start from its first
candidate on. -/
theorem searchRange_none {m : BootMemory} {size al bound : Nat} (hs : 0 < size)
    (hal : 0 < al) : ∀ fuel c, m.searchRange size al bound fuel c = .ok none →
      ∀ u, c ≤ u → ¬ SearchAccepts m size al bound u
  | 0, c, h => by simp [BootMemory.searchRange] at h
  | fuel + 1, c, h => by
    intro u hcu hg
    rw [BootMemory.searchRange] at h
    dsimp only at h
    split at h
    · rename_i hstop
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hstop
      obtain ⟨-, hglt, hgle, -⟩ := hg
      omega
    · rename_i hstop
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Nat.not_lt] at hstop
      split at h
      · cases h
      · rename_i hne
        obtain ⟨next, hnext, h⟩ := except_bind_ok.1 h
        have hne' := Bool.of_not_eq_true hne
        obtain ⟨-, hskip⟩ := skip_not_accepted (bound := bound) hs hal hstop.1 hne' hnext
        by_cases hu : u < next
        · exact hskip u hcu hu hg
        · exact searchRange_none hs hal fuel next h u (by omega) hg

/-- A search of one range that gives a span gives the candidate at the least
start from its first candidate on that it accepts. -/
theorem searchRange_some {m : BootMemory} {size al bound : Nat} (hs : 0 < size)
    (hal : 0 < al) : ∀ fuel c s, m.searchRange size al bound fuel c = .ok (some s) →
      c % al = 0 →
      ∃ t, s = ⟨UInt64.ofNat t, UInt64.ofNat size⟩ ∧ c ≤ t ∧
        SearchAccepts m size al bound t ∧ ∀ u, c ≤ u → u < t → ¬ SearchAccepts m size al bound u
  | 0, c, s, h, _ => by simp [BootMemory.searchRange] at h
  | fuel + 1, c, s, h, hcm => by
    rw [BootMemory.searchRange] at h
    dsimp only at h
    split at h
    · cases h
    · rename_i hstop
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Nat.not_lt] at hstop
      split at h
      · rename_i hemp
        injection h with h
        injection h with h
        subst h
        refine ⟨c, rfl, Nat.le_refl _, ⟨hcm, hstop.1, hstop.2, ?_⟩, fun u h1 h2 => by omega⟩
        intro x hx
        rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hemp
        simpa using hemp x hx
      · rename_i hne
        obtain ⟨next, hnext, h⟩ := except_bind_ok.1 h
        have hne' := Bool.of_not_eq_true hne
        obtain ⟨hcn, hskip⟩ := skip_not_accepted (bound := bound) hs hal hstop.1 hne' hnext
        obtain ⟨-, hnm, -, -⟩ := alignUp_ok hal hnext
        obtain ⟨t, rfl, hnt, hg, hlow⟩ := searchRange_some hs hal fuel next s h hnm
        refine ⟨t, rfl, by omega, hg, fun u h1 h2 => ?_⟩
        by_cases hu : u < next
        · exact hskip u h1 hu
        · exact hlow u (by omega) h2

/-- A search through ranges that gives a span gives it from the first range
whose search gives one; the search of each range before it ends with none. -/
theorem searchRanges_some {m : BootMemory} {size al minimum limit : Nat} :
    ∀ (l : List Span) s, m.searchRanges size al minimum limit l = .ok (some s) →
      ∃ i r c0, l[i]? = some r ∧ alignUp (max r.start.toNat minimum) al = .ok c0 ∧
        m.searchRange size al (min r.endNat limit) (m.reserved.length + 3) c0 = .ok (some s) ∧
        ∀ r' ∈ l.take i, ∃ c1, alignUp (max r'.start.toNat minimum) al = .ok c1 ∧
          m.searchRange size al (min r'.endNat limit) (m.reserved.length + 3) c1 = .ok none
  | [], s, h => by simp [BootMemory.searchRanges] at h
  | r :: rest, s, h => by
    rw [BootMemory.searchRanges] at h
    obtain ⟨c0, hc0, h⟩ := except_bind_ok.1 h
    obtain ⟨x, hx, h⟩ := except_bind_ok.1 h
    cases x with
    | some s' =>
      rw [except_pure_ok] at h
      injection h with h
      subst h
      exact ⟨0, r, c0, rfl, hc0, hx, by simp⟩
    | none =>
      obtain ⟨i, r1, c1, hi, h1, h2, hb⟩ := searchRanges_some rest s h
      refine ⟨i + 1, r1, c1, by simpa using hi, h1, h2, ?_⟩
      intro r' hr'
      rw [List.take_succ_cons, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · exact ⟨c0, hc0, hx⟩
      · exact hb r' hr'

/-- A search through ranges that ends with none ends with none in each range. -/
theorem searchRanges_none {m : BootMemory} {size al minimum limit : Nat} :
    ∀ (l : List Span), m.searchRanges size al minimum limit l = .ok none →
      ∀ r ∈ l, ∃ c1, alignUp (max r.start.toNat minimum) al = .ok c1 ∧
        m.searchRange size al (min r.endNat limit) (m.reserved.length + 3) c1 = .ok none
  | [], _ => by simp
  | r :: rest, h => by
    rw [BootMemory.searchRanges] at h
    obtain ⟨c0, hc0, h⟩ := except_bind_ok.1 h
    obtain ⟨x, hx, h⟩ := except_bind_ok.1 h
    cases x with
    | some s' =>
      rw [except_pure_ok] at h
      cases h
    | none =>
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨c0, hc0, hx⟩
      · exact searchRanges_none rest h r' hr'

/-- The checks of `find_available` before its search: a nonzero size, an
alignment above 0, and then the search through the RAM ranges. -/
theorem findAvailable_ok {m : BootMemory} {size alignment minimum limit : UInt64}
    {v : Option Span} (h : m.findAvailable size alignment minimum limit = .ok v) :
    size ≠ 0 ∧ 0 < alignment.toNat ∧
      m.searchRanges size.toNat alignment.toNat minimum.toNat limit.toNat m.ram = .ok v := by
  unfold BootMemory.findAvailable at h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨h2, h⟩ := except_jp_ok h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
  have h2' : isPowerOfTwo alignment = true := by simpa using h2
  refine ⟨h1.1, ?_, h⟩
  simp only [isPowerOfTwo, List.any_eq_true, beq_iff_eq] at h2'
  obtain ⟨k, -, hk⟩ := h2'
  rw [hk]
  exact Nat.two_pow_pos k

/-- A span that fits a range has a start that the search of that range accepts,
at or above its first candidate. -/
theorem accepts_of_fits {m : BootMemory} {size alignment minimum limit : UInt64} {r s : Span}
    {c0 : Nat} (hal : 0 < alignment.toNat)
    (hc0 : alignUp (max r.start.toNat minimum.toNat) alignment.toNat = .ok c0)
    (hf : m.Fits size alignment minimum limit r s) :
    s = ⟨UInt64.ofNat s.start.toNat, UInt64.ofNat size.toNat⟩ ∧ c0 ≤ s.start.toNat ∧
      SearchAccepts m size.toNat alignment.toNat (min r.endNat limit.toNat) s.start.toNat := by
  obtain ⟨hsz, hmod, hmin, hlim, hval, hhold, hx⟩ := hf
  rw [holds_iff] at hhold
  have hs : s = ⟨UInt64.ofNat s.start.toNat, UInt64.ofNat size.toNat⟩ := by
    rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat, ← hsz]
  have hse : s.endNat = s.start.toNat + size.toNat := by unfold Span.endNat; rw [hsz]
  unfold Span.Valid at hval
  rw [hse] at hval hlim hhold
  refine ⟨hs, (alignUp_ok hal hc0).2.2.2 _ (by omega) hmod, hmod, hval, by omega, ?_⟩
  intro x hxm
  rw [← hs]
  exact hx x hxm

/-- A start that the search of a range accepts, at or above its first candidate,
gives a span that fits the range. -/
theorem fits_of_accepts {m : BootMemory} {size alignment minimum limit : UInt64} {r : Span}
    {c0 t : Nat} (hal : 0 < alignment.toNat)
    (hc0 : alignUp (max r.start.toNat minimum.toNat) alignment.toNat = .ok c0) (hct : c0 ≤ t)
    (hg : SearchAccepts m size.toNat alignment.toNat (min r.endNat limit.toNat) t) :
    m.Fits size alignment minimum limit r ⟨UInt64.ofNat t, UInt64.ofNat size.toNat⟩ := by
  obtain ⟨hmod, hlt, hle, hx⟩ := hg
  obtain ⟨hcs, hcz, hce⟩ := cand_toNat hlt
  have h0 := (alignUp_ok hal hc0).1
  refine ⟨UInt64.ofNat_toNat, by rw [hcs]; exact hmod, by rw [hcs]; omega, by rw [hce]; omega,
    by unfold Span.Valid; rw [hce]; exact hlt, ?_, hx⟩
  rw [holds_iff, hcs, hce]
  omega

end Krepi.Proofs.Fdt

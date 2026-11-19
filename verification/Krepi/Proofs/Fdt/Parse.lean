module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.ParseBytes
import Krepi.Proofs.Fdt.ParseSteps
import Krepi.Proofs.Fdt.ParseWalk
import Krepi.Proofs.Fdt.ParseLimits
import Krepi.Proofs.Fdt.ParseProperties

/-!
# Device tree: proofs about the parse

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the parse, whose type is exactly that statement: that the tree of the
parse is well-formed, that each of its limits is exact, and that every
prefix of an accepted tree is rejected.

Every theorem here is proved. The invariants of the walk of the parse are in
`Krepi.Proofs.Fdt.ParseWalk`; the evaluation of the parse of the trees at the
limits, in `Krepi.Proofs.Fdt.ParseLimits` and
`Krepi.Proofs.Fdt.ParseProperties`, through the lemmas about built trees of
`Krepi.Proofs.Fdt.ParseBuilt`. Mathlib is imported so that the gate counts
the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Parse

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem parseWellFormed : ParseWellFormed := by
  intro input t h
  obtain ⟨hd, hh, h⟩ := except_bind_ok.1 h
  obtain ⟨rs, hrs, h⟩ := except_bind_ok.1 h
  obtain ⟨recs, hrecs, h⟩ := except_bind_ok.1 h
  cases except_pure_ok.1 h
  obtain ⟨-, -, -, ht40, htmax, -⟩ := header_ok hh
  have htn : (UInt64.ofNat hd.layout.total).toNat = hd.layout.total := by
    apply UInt64.toNat_ofNat_of_lt'
    simp [MAX_BLOB_SIZE] at htmax
    simp [UInt64.size]
    omega
  obtain ⟨hrl, hrn, hrp⟩ :=
    reservationsFrom_ok hd _ _ _ rs ⟨by simp, by simp, by simp⟩ hrs
  obtain ⟨hn, hpos, hmax⟩ := walkTokens_ok _ _ _ _ walkOk_start (by simp [Walk.start]) hrecs
  refine ⟨by rw [htn]; exact ht40, ?_, hrl, hrn, hrp, hpos, hmax, ?_⟩
  · rw [UInt64.le_iff_toNat_le, htn]; exact htmax
  · intro i hi
    have := hn i hi
    unfold Fdt.NodeWellFormed Fdt.depth
    rw [depthFrom_eq_recDepth]
    exact this

public theorem parseLimitsExact : ParseLimitsExact :=
  ⟨parse_size_limit, parse_size_over, parse_depth_limit, parse_depth_over, parse_tokens_limit,
    parse_tokens_over, parse_properties_limit, parse_properties_over, parse_name_limit,
    parse_name_over, parse_reservations_limit, parse_reservations_over⟩

public theorem prefixesRejected : PrefixesRejected := by
  intro input t h n hn
  obtain ⟨hd, hh, h⟩ := except_bind_ok.1 h
  obtain ⟨rs, -, h⟩ := except_bind_ok.1 h
  obtain ⟨recs, -, h⟩ := except_bind_ok.1 h
  have h := except_pure_ok.1 h
  subst h
  obtain ⟨h40, hm, ⟨v, hv, hvt⟩, ht40, htmax, htsize⟩ := header_ok hh
  have htn : (UInt64.ofNat hd.layout.total).toNat = hd.layout.total := by
    apply UInt64.toNat_ofNat_of_lt'
    simp [MAX_BLOB_SIZE] at htmax
    simp [UInt64.size]
    omega
  simp only [htn] at hn
  have hns := size_prefix (input := input) (n := n) (by omega)
  suffices hp : header (input.extract 0 n) = .error .truncated by
    simp [Fdt.parse, hp, bind, Except.bind]
  unfold header
  by_cases h40n : n < HEADER_SIZE
  · simp [hns, h40n, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · rw [u32At_prefix (by omega) (by simp [HEADER_SIZE] at h40n; omega),
      u32At_prefix (by omega) (by simp [HEADER_SIZE] at h40n; omega), hm, hv]
    simp [hvt, hns, h40n, Nat.not_lt.2 ht40, Nat.not_lt.2 htmax, hn, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]

end Krepi.Proofs.Fdt.Parse

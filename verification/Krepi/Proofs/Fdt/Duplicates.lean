module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.Fdt.PathLemmas
import Krepi.Proofs.Fdt.DiscoveryLemmas

/-!
# Device tree: proofs about duplicates and ambiguities

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about duplicates and ambiguities, whose type is exactly that statement: that
where an entry looks for one item and finds two, it rejects the input and
never picks one.

The theorem is planned: its proof is `sorry` until a proof pull request
proves it, from these lemmas. The paths: the components of the path of a
node lead from the root to it (`Krepi.Proofs.Fdt.PathLemmas`), so two nodes
of one path make the walk of the lookup meet two children of one name, and a
node that it finds is the node of its path (`paths_unique`). The CPU nodes,
the RAM ranges and the banks follow from the lemmas of
`Krepi.Proofs.Fdt.DiscoveryLemmas` and `Krepi.Proofs.Fdt.PlanLemmas`.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Duplicates

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- On a well-formed tree, two nodes of one path make its lookup fail with
`AmbiguousMapping`, and a node that a lookup finds is the only node of its
path. -/
theorem paths_unique (t : Fdt) (ht : t.WellFormed) :
    (∀ n ∈ t.nodes, ∀ m ∈ t.nodes, n.index.val ≠ m.index.val → n.path = m.path →
      t.findNode n.path = .error .ambiguousMapping) ∧
    ∀ (path : String) (n : Node), t.findNode path = .ok (some n) →
      ∀ m ∈ t.nodes, m.path = path → m.index.val = n.index.val := by
  have h0 : 0 < t.records.size := ht.2.2.2.2.2.1
  have hroot : t.root = some ⟨t, ⟨0, h0⟩⟩ := by simp [Fdt.root, h0]
  refine ⟨fun n hn m hm hne hpath => ?_, fun path n h m hm hpath => ?_⟩
  · obtain ⟨cs, hr, hz, hs, hc⟩ := path_spec ht h0 hn
    obtain ⟨cs', hr', hz', hs', hc'⟩ := path_spec ht h0 hm
    by_cases hcs : cs = []
    · have hn1 := hs hcs
      by_cases hcs' : cs' = []
      · exact absurd ((hz.1 hcs).trans (hz'.1 hcs').symm) hne
      · obtain ⟨hp', hcc'⟩ := hc' hcs'
        rw [← hpath, hn1] at hp'
        obtain ⟨-, -, hne'⟩ := path_props cs' hcs' hcc'
        exact absurd (List.cons.inj hp').2.symm hne'
    · obtain ⟨hp, hcc⟩ := hc hcs
      by_cases hcs' : cs' = []
      · have hm1 := hs' hcs'
        rw [hpath, hm1] at hp
        obtain ⟨-, -, hne'⟩ := path_props cs hcs hcc
        exact absurd (List.cons.inj hp).2.symm hne'
      · obtain ⟨hp', hcc'⟩ := hc' hcs'
        have heq : cs' = cs := by
          have hp2 := hp
          rw [hpath, hp'] at hp2
          have := congrArg splitSlash (List.cons.inj hp2).2
          rwa [splitSlash_intercalate _ hcs' (fun c h => (hcc' c h).2),
            splitSlash_intercalate _ hcs (fun c h => (hcc c h).2)] at this
        subst heq
        rw [findNode_comps hp hcs hcc, hroot]
        exact descend_ambiguous hr hr' hne
  · subst hpath
    obtain ⟨cs, hr, hz, hs, hc⟩ := path_spec ht h0 hm
    by_cases hcs : cs = []
    · rw [findNode_slash (hs hcs), hroot] at h
      cases h
      exact hz.1 hcs
    · obtain ⟨hp, hcc⟩ := hc hcs
      rw [findNode_comps hp hcs hcc, hroot] at h
      rw [descend_found hr h]

public theorem noChoiceAmongDuplicates : NoChoiceAmongDuplicates := by
  sorry

end Krepi.Proofs.Fdt.Duplicates

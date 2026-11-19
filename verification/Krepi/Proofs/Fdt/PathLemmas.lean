module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: lemmas about paths and their lookup

Lemmas about the absolute paths of the nodes of a tree of the specification
of the `fdt` component and about `Fdt::find_node`, for the proofs of the
statements that look nodes up:

- `Reach t x cs z`: `z` lies below `x` along the components `cs`, each a
  child of the node before it whose name has the characters of its
  component; `Reach.snoc` adds a component at the end;
- the walk of `Fdt.descend` along such components: two distinct nodes below
  one node along the same components make it fail with `AmbiguousMapping`
  (`descend_ambiguous`), and a node that it finds is the one below
  (`descend_found`);
- paths as characters: `splitSlash` of components joined by `/` gives them
  back (`splitSlash_intercalate`), such a path is valid (`path_props`,
  `pathValid_of_comps`), and its lookup is `Fdt.descend` from the root
  (`findNode_comps`), the lookup of `/` the root (`findNode_slash`); a node
  that the lookup of a path of one component finds is a child of the root
  with that name (`findNode_single`);
- the path of a node of a well-formed tree: its components lead from the
  root to it (`namesFrom_spec`, `path_spec`).
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt

/-- `z` lies below `x` along the components `cs`: each a child of the node
before it whose name has the characters of its component. -/
inductive Reach (t : Fdt) : Node → List (List Char) → Node → Prop
  | nil (x : Node) : Reach t x [] x
  | cons {x y z : Node} {c : List Char} {cs : List (List Char)} :
      y ∈ t.nodes → y.isChildOf x = true → y.name.toList = c → Reach t y cs z →
      Reach t x (c :: cs) z

/-- A child of the end of a walk extends it by its name. -/
theorem Reach.snoc {t : Fdt} {x y z : Node} {cs : List (List Char)} (h : Reach t x cs y)
    (hz : z ∈ t.nodes) (hc : z.isChildOf y = true) : Reach t x (cs ++ [z.name.toList]) z := by
  induction h with
  | nil x => exact .cons hz hc rfl (.nil z)
  | cons hy hyx hn _ ih => exact .cons hy hyx hn (ih hc)

/-- Two distinct nodes below `x` along the same components make the walk from
`x` fail with `AmbiguousMapping`. -/
theorem descend_ambiguous {t : Fdt} : ∀ {cs : List (List Char)} {x n m : Node},
    Reach t x cs n → Reach t x cs m → n.index.val ≠ m.index.val →
    t.descend cs (some x) = .error .ambiguousMapping
  | [], _, _, _, hn, hm, hne => by
    cases hn
    cases hm
    exact absurd rfl hne
  | c :: cs, x, n, m, hn, hm, hne => by
    cases hn with
    | @cons _ y1 _ _ _ hy1 hc1 hn1 hr1 =>
    cases hm with
    | @cons _ y2 _ _ _ hy2 hc2 hn2 hr2 =>
    have hm1 : y1 ∈ t.nodes.filter (fun n => n.isChildOf x && n.name.toList == c) :=
      List.mem_filter.2 ⟨hy1, by simp [hc1, hn1]⟩
    have hm2 : y2 ∈ t.nodes.filter (fun n => n.isChildOf x && n.name.toList == c) :=
      List.mem_filter.2 ⟨hy2, by simp [hc2, hn2]⟩
    rw [Fdt.descend]
    split
    · rename_i hF
      rw [hF] at hm1
      exact absurd hm1 List.not_mem_nil
    · rename_i w hF
      rw [hF, List.mem_singleton] at hm1 hm2
      subst hm1
      subst hm2
      exact descend_ambiguous hr1 hr2 hne
    · rfl

/-- The node that the walk from `x` along the components to a node finds is
that node. -/
theorem descend_found {t : Fdt} : ∀ {cs : List (List Char)} {x n y : Node},
    Reach t x cs n → t.descend cs (some x) = .ok (some y) → y = n
  | [], _, _, _, hn, h => by
    cases hn
    rw [Fdt.descend] at h
    cases h
    rfl
  | c :: cs, x, n, y, hn, h => by
    cases hn with
    | @cons _ y1 _ _ _ hy1 hc1 hn1 hr1 =>
    have hm1 : y1 ∈ t.nodes.filter (fun n => n.isChildOf x && n.name.toList == c) :=
      List.mem_filter.2 ⟨hy1, by simp [hc1, hn1]⟩
    rw [Fdt.descend] at h
    split at h
    · rename_i hF
      rw [hF] at hm1
      exact absurd hm1 List.not_mem_nil
    · rename_i w hF
      rw [hF, List.mem_singleton] at hm1
      subst hm1
      exact descend_found hr1 h
    · cases h

/-! ## Paths as characters -/

/-- One step of `splitSlash` on a character other than `/`. -/
theorem splitSlash_cons {a : Char} (ha : a ≠ '/') (l : List Char) :
    splitSlash (a :: l) = match splitSlash l with
      | [] => [[a]]
      | w :: ws => (a :: w) :: ws :=
  splitSlash.eq_3 a l ha

/-- Characters without `/` are one component. -/
theorem splitSlash_of_no_slash : ∀ (c : List Char), '/' ∉ c → splitSlash c = [c]
  | [], _ => rfl
  | a :: c, h => by
    have ha : a ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    rw [splitSlash_cons ha, splitSlash_of_no_slash c (fun e => h (List.mem_cons_of_mem _ e))]

/-- A component without `/`, then `/`, splits off as the first component. -/
theorem splitSlash_append : ∀ (c rest : List Char), '/' ∉ c →
    splitSlash (c ++ '/' :: rest) = c :: splitSlash rest
  | [], rest, _ => rfl
  | a :: c, rest, h => by
    have ha : a ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    rw [List.cons_append, splitSlash_cons ha,
      splitSlash_append c rest (fun e => h (List.mem_cons_of_mem _ e))]

/-- Components without `/` joined by `/` split back into themselves. -/
theorem splitSlash_intercalate :
    ∀ (cs : List (List Char)), cs ≠ [] → (∀ c ∈ cs, '/' ∉ c) →
    splitSlash (['/'].intercalate cs) = cs
  | [], h, _ => absurd rfl h
  | [c], _, h => by
    rw [List.intercalate_singleton, splitSlash_of_no_slash c (h c List.mem_cons_self)]
  | c :: d :: rest, _, h => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
      splitSlash_append c _ (h c List.mem_cons_self),
      splitSlash_intercalate (d :: rest) (List.cons_ne_nil _ _)
        (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A character other than `/` starts no `//`. -/
theorem hasDoubleSlash_cons {a : Char} (ha : a ≠ '/') (l : List Char) :
    hasDoubleSlash (a :: l) = hasDoubleSlash l :=
  hasDoubleSlash.eq_2 a l (fun _ e _ => ha e)

/-- Characters without `/` before a list add no `//`. -/
theorem hasDoubleSlash_append : ∀ (w L : List Char), '/' ∉ w →
    hasDoubleSlash (w ++ L) = hasDoubleSlash L
  | [], _, _ => rfl
  | a :: w, L, h => by
    have ha : a ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    rw [List.cons_append, hasDoubleSlash_cons ha,
      hasDoubleSlash_append w L (fun e => h (List.mem_cons_of_mem _ e))]

/-- `/` and a nonempty component without `/` before a list add no `//`. -/
theorem hasDoubleSlash_slash {c L : List Char} (hc : c ≠ []) (h : '/' ∉ c) :
    hasDoubleSlash ('/' :: (c ++ L)) = hasDoubleSlash L := by
  obtain ⟨a, c', rfl⟩ := List.exists_cons_of_ne_nil hc
  have ha : a ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
  rw [List.cons_append, hasDoubleSlash.eq_2 '/' _ (fun _ _ e => ha (List.cons.inj e).1),
    hasDoubleSlash_cons ha, hasDoubleSlash_append c' L (fun e => h (List.mem_cons_of_mem _ e))]

/-- `/` and nonempty components without `/` joined by `/`: no `//`, a last
character other than `/`, and more than the first `/`. -/
theorem path_props :
    ∀ (cs : List (List Char)), cs ≠ [] → (∀ c ∈ cs, c ≠ [] ∧ '/' ∉ c) →
    hasDoubleSlash ('/' :: ['/'].intercalate cs) = false ∧
      (∃ y, ('/' :: ['/'].intercalate cs).getLast? = some y ∧ y ≠ '/') ∧
      ['/'].intercalate cs ≠ []
  | [], h, _ => absurd rfl h
  | [c], _, h => by
    obtain ⟨hc1, hc2⟩ := h c List.mem_cons_self
    rw [List.intercalate_singleton]
    refine ⟨?_, ?_, hc1⟩
    · have := hasDoubleSlash_slash (L := []) hc1 hc2
      rw [List.append_nil] at this
      rw [this]
      rfl
    · obtain ⟨y, hy⟩ := List.getLast?_isSome.2 hc1 |> Option.isSome_iff_exists.1
      refine ⟨y, ?_, fun e => hc2 (e ▸ List.mem_of_getLast? hy)⟩
      rw [List.getLast?_cons, hy]
      rfl
  | c :: d :: rest, _, h => by
    obtain ⟨hc1, hc2⟩ := h c List.mem_cons_self
    obtain ⟨ih1, ⟨y, hy, hy'⟩, _⟩ := path_props (d :: rest) (List.cons_ne_nil _ _)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append]
    refine ⟨?_, ⟨y, ?_, hy'⟩, ?_⟩
    · rw [hasDoubleSlash_slash hc1 hc2, ih1]
    · rw [← List.cons_append, List.getLast?_append, hy]
      rfl
    · simp

/-- `/` and nonempty components without `/` joined by `/` is a valid path. -/
theorem pathValid_of_comps {cs : List (List Char)} (hcs : cs ≠ [])
    (hc : ∀ c ∈ cs, c ≠ [] ∧ '/' ∉ c) :
    pathValid ('/' :: ['/'].intercalate cs) = true := by
  obtain ⟨h1, ⟨y, hy, hy'⟩, _⟩ := path_props cs hcs hc
  unfold pathValid
  rw [h1, hy]
  simp [hy']

/-- The lookup of `/` and nonempty components without `/` joined by `/` is the
walk along them from the root. -/
theorem findNode_comps {t : Fdt} {path : String} {cs : List (List Char)}
    (hp : path.toList = '/' :: ['/'].intercalate cs) (hcs : cs ≠ [])
    (hc : ∀ c ∈ cs, c ≠ [] ∧ '/' ∉ c) : t.findNode path = t.descend cs t.root := by
  obtain ⟨_, _, hne⟩ := path_props cs hcs hc
  unfold Fdt.findNode
  simp only [hp, pathValid_of_comps hcs hc, Bool.not_true, Bool.false_eq_true, ite_false,
    List.tail_cons]
  rw [ite_eq_right_iff.2, splitSlash_intercalate cs hcs (fun c h => (hc c h).2)]
  intro h
  simp only [beq_iff_eq, List.cons.injEq, true_and] at h
  exact absurd h hne

/-- The lookup of `/` is the root. -/
theorem findNode_slash {t : Fdt} {path : String} (hp : path.toList = ['/']) :
    t.findNode path = .ok t.root := by
  unfold Fdt.findNode
  simp only [hp]
  rfl

/-! ## Paths of nodes -/

/-- A node of a tree by its index is one of its nodes. -/
theorem node_mem (t : Fdt) (i : Fin t.records.size) : (⟨t, i⟩ : Node) ∈ t.nodes := by
  simp [Fdt.nodes]

/-- The names from the root to a node of a well-formed tree: nonempty and
without `/`, none only for the root, and their characters lead from the root
to the node. -/
theorem namesFrom_spec {t : Fdt} (ht : t.WellFormed) (h0 : 0 < t.records.size) :
    ∀ (fuel i : Nat) (hi : i < t.records.size), i < fuel →
    Reach t ⟨t, ⟨0, h0⟩⟩ ((t.namesFrom fuel i).map String.toList) ⟨t, ⟨i, hi⟩⟩ ∧
    (∀ s ∈ t.namesFrom fuel i, s.toList ≠ [] ∧ '/' ∉ s.toList) ∧
    (t.namesFrom fuel i = [] ↔ i = 0)
  | 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, i, hi, hf => by
    obtain ⟨hpar, hchars, -⟩ := ht.2.2.2.2.2.2.2 i hi
    rw [Fdt.namesFrom, Array.getElem?_eq_getElem hi]
    by_cases h0i : i = 0
    · subst h0i
      simp only [↓reduceIte] at hpar
      simp only [hpar.1]
      exact ⟨.nil _, by simp, by simp⟩
    · simp only [h0i, ↓reduceIte] at hpar
      obtain ⟨⟨p, hp, hpi⟩, hname⟩ := hpar
      simp only [hp]
      have hpf : p < fuel := by omega
      have hps : p < t.records.size := by omega
      obtain ⟨ih1, ih2, -⟩ := namesFrom_spec ht h0 fuel p hps hpf
      refine ⟨?_, ?_, ?_⟩
      · rw [List.map_append]
        exact ih1.snoc (node_mem t ⟨i, hi⟩) (by simp [Node.isChildOf, Node.record, hp])
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact ih2 s hs
        · rw [List.mem_singleton] at hs
          subst hs
          refine ⟨fun e => hname (String.toList_eq_nil_iff.1 e), fun e => ?_⟩
          have := List.all_eq_true.1 hchars '/' e
          exact absurd this (by decide)
      · simp [h0i]

/-- The path of a node of a well-formed tree: `/` for the root, otherwise `/`
and the components that lead from the root to it, nonempty and without `/`,
joined by `/`. -/
theorem path_spec {t : Fdt} (ht : t.WellFormed) (h0 : 0 < t.records.size) {n : Node}
    (hn : n ∈ t.nodes) :
    ∃ cs, Reach t ⟨t, ⟨0, h0⟩⟩ cs n ∧ (cs = [] ↔ n.index.val = 0) ∧
      (cs = [] → n.path.toList = ['/']) ∧
      (cs ≠ [] → n.path.toList = '/' :: ['/'].intercalate cs ∧
        ∀ c ∈ cs, c ≠ [] ∧ '/' ∉ c) := by
  simp only [Fdt.nodes, List.mem_map, List.mem_finRange, true_and] at hn
  obtain ⟨⟨i, hi⟩, rfl⟩ := hn
  obtain ⟨h1, h2, h3⟩ := namesFrom_spec ht h0 (i + 1) i hi (Nat.lt_succ_self i)
  refine ⟨_, h1, ?_, ?_, ?_⟩
  · rw [List.map_eq_nil_iff]
    exact h3
  · intro h
    rw [List.map_eq_nil_iff] at h
    simp only [Node.path, h, String.intercalate_nil, String.toList_append]
    rfl
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Node.path, String.toList_append, String.toList_intercalate]
      rfl
    · intro c hc
      rw [List.mem_map] at hc
      obtain ⟨s, hs, rfl⟩ := hc
      exact h2 s hs

/-- A node that the lookup of a path of one component finds is a child of the
root whose name has the characters of that component. -/
theorem findNode_single {t : Fdt} (ht : t.WellFormed) {path : String} {c : List Char}
    {n : Node} (hp : path.toList = '/' :: c) (hc : c ≠ []) (hs : '/' ∉ c)
    (h : t.findNode path = .ok (some n)) :
    n ∈ t.nodes ∧ n.record.parent = some 0 ∧ n.name.toList = c := by
  have h0 : 0 < t.records.size := ht.2.2.2.2.2.1
  have hroot : t.root = some ⟨t, ⟨0, h0⟩⟩ := by simp [Fdt.root, h0]
  rw [findNode_comps (cs := [c]) (by rw [hp, List.intercalate_singleton])
    (List.cons_ne_nil _ _) (by simpa using And.intro hc hs), hroot, Fdt.descend] at h
  split at h
  · rw [Fdt.descend] at h
    cases h
  · rename_i w hF
    rw [Fdt.descend] at h
    simp only [Except.ok.injEq, Option.some.injEq] at h
    subst h
    have hw : w ∈ t.nodes.filter
        (fun n => n.isChildOf ⟨t, ⟨0, h0⟩⟩ && n.name.toList == c) := by
      rw [hF]
      exact List.mem_singleton_self w
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw2
    exact ⟨hw1, by simpa [Node.isChildOf] using hw2.1, hw2.2⟩
  · cases h

end Krepi.Proofs.Fdt

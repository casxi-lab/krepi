module

public import Krepi.Proofs.Fdt.Refinement.Utf8Lemmas
public import Krepi.Spec.Fdt.Nodes
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: the nodes of a parsed tree

Lemmas about the specification of the `fdt` component that the triples of the
node walk need, for the proofs below `Krepi.Proofs.Fdt.Refinement`: the
inversion of `Fdt.parse` that gives the begin-node tokens of a tree, with
their offsets, names and parents, from which the representation of a node
(`NodeRepr`) reads them. The module imports no generated definitions, so it
is built once and not again for every mutant of the code.

- The walk of the code: `Begin`, a begin-node token with its offset, name and
  the offset of its parent, and `nodesFrom`, the begin-node tokens from a
  cursor with the offsets of the open nodes, as the code walks the tokens
  (an end node closes the innermost open node, a begin node opens one), none
  when a token is refused, the fuel runs out or a node lies `MAX_DEPTH` deep.
  Its equations: `nodesFrom_zero`, `nodesFrom_begin`, `nodesFrom_endNode`,
  `nodesFrom_property`, `nodesFrom_nop`, `nodesFrom_end`, and for a walk that
  succeeds `nodesFrom_decode`, `nodesFrom_begin_some` and
  `nodesFrom_end_some`.
- What a walk that succeeds gives: `nodesFrom_sorted` (the offsets lie at or
  after the cursor, increase, and are fewer than the fuel), `nodesFrom_mem`
  (`decodeToken` reads a begin node with the name at each offset),
  `find?_offset` (the first token at the offset of one is that one) and
  `offsets_of_nodesFrom` (the offsets are those of `beginOffsets` of the
  statements, stated for any function with its equations, since the
  statements import the generated code).
- Tokens: `decodeToken_tag_ok`, `decodeToken_next_ge` and
  `decodeToken_begin` (the name of a begin node after its tag, its NUL, and
  the next token at the next multiple of 4).
- The inversion of the parse: `BeginsOf`, begin-node tokens that stand for
  the records of a tree (one each, with its name and the offset of the token
  of its parent), and `WalkRel`, the invariant between a walk of the parse,
  the tokens read so far and the offsets of the open nodes; the steps
  `place_begin_eq`, `place_property_eq`, `place_endNode_eq`,
  `getElem?_map_append`, `walkRel_begin`, `walkRel_property`,
  `walkRel_endNode` and `walkRel_start`; `nodesFrom_walkTokens`, the walk of
  `nodesFrom` succeeds where `walkTokens` does and stands for its records; and
  `parse_nodesFrom`, the same for the structure block of a tree that
  `Fdt.parse` accepts.
- The nodes of a tree: `nodes_length`, `nodes_getElem`, `nodes_drop_cons`
  and `nodes_drop_nil`.
- The header: `block_size_le` and `header_sizes` (the bytes of a tree are at
  most `MAX_BLOB_SIZE`, its blocks within them).
-/

@[expose] public section

open Krepi.Spec.Fdt Krepi.Proofs.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The begin-node tokens of a structure block -/

/-- A begin-node token of a structure block: its offset, the name that
`decodeToken` reads in it, and the offset of the begin-node token of the
innermost open node before it, none outside every node. -/
structure Begin where
  offset : Nat
  «name» : String
  parent : Option Nat
  deriving Inhabited

/-- The begin-node tokens from the token at `cursor` on, with the offsets of
the open nodes `stack`, innermost first, reading at most `fuel` tokens as
`decodeToken` reads them, as the code walks them: an end node closes the
innermost open node, a begin node opens one. None when a token is refused,
when the fuel runs out before the end token, or when a begin node lies
`MAX_DEPTH` deep; otherwise the begin-node tokens before the end token. -/
def nodesFrom (str strs : ByteArray) : (fuel cursor : Nat) → List Nat → Option (List Begin)
  | 0, _, _ => none
  | fuel + 1, cursor, stack =>
    match decodeToken str strs cursor with
    | .ok (.beginNode nm, next) =>
      if stack.length < MAX_DEPTH.toNat then
        (nodesFrom str strs fuel next (cursor :: stack)).map (⟨cursor, nm, stack.head?⟩ :: ·)
      else none
    | .ok (.endNode, next) => nodesFrom str strs fuel next stack.tail
    | .ok (.property _ _, next) => nodesFrom str strs fuel next stack
    | .ok (.nop, next) => nodesFrom str strs fuel next stack
    | .ok (.endStructure, _) => some []
    | .error _ => none

section NodesFrom

variable {str strs : ByteArray}

theorem nodesFrom_zero (c : Nat) (st : List Nat) : nodesFrom str strs 0 c st = none := rfl

theorem nodesFrom_begin {f c next : Nat} {st : List Nat} {nm : String}
    (hd : decodeToken str strs c = .ok (.beginNode nm, next)) :
    nodesFrom str strs (f + 1) c st =
      if st.length < MAX_DEPTH.toNat then
        (nodesFrom str strs f next (c :: st)).map (⟨c, nm, st.head?⟩ :: ·)
      else none := by
  rw [nodesFrom, hd]

theorem nodesFrom_endNode {f c next : Nat} {st : List Nat}
    (hd : decodeToken str strs c = .ok (.endNode, next)) :
    nodesFrom str strs (f + 1) c st = nodesFrom str strs f next st.tail := by
  rw [nodesFrom, hd]

theorem nodesFrom_property {f c next : Nat} {st : List Nat} {nm : String} {value : ByteArray}
    (hd : decodeToken str strs c = .ok (.property nm value, next)) :
    nodesFrom str strs (f + 1) c st = nodesFrom str strs f next st := by
  rw [nodesFrom, hd]

theorem nodesFrom_nop {f c next : Nat} {st : List Nat}
    (hd : decodeToken str strs c = .ok (.nop, next)) :
    nodesFrom str strs (f + 1) c st = nodesFrom str strs f next st := by
  rw [nodesFrom, hd]

theorem nodesFrom_end {f c next : Nat} {st : List Nat}
    (hd : decodeToken str strs c = .ok (.endStructure, next)) :
    nodesFrom str strs (f + 1) c st = some [] := by
  rw [nodesFrom, hd]

/-- A walk that succeeds at a begin-node token: the token is below
`MAX_DEPTH`, and its begin-node token comes first. -/
theorem nodesFrom_begin_some {f c next : Nat} {st : List Nat} {nm : String} {L : List Begin}
    (hd : decodeToken str strs c = .ok (.beginNode nm, next))
    (h : nodesFrom str strs (f + 1) c st = some L) :
    st.length < MAX_DEPTH.toNat ∧
      ∃ L', L = ⟨c, nm, st.head?⟩ :: L' ∧ nodesFrom str strs f next (c :: st) = some L' := by
  rw [nodesFrom_begin hd] at h
  split at h
  · obtain ⟨L', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨‹_›, L', rfl, h'⟩
  · cases h

/-- A walk that succeeds at the end token has no begin-node token left. -/
theorem nodesFrom_end_some {f c next : Nat} {st : List Nat} {L : List Begin}
    (hd : decodeToken str strs c = .ok (.endStructure, next))
    (h : nodesFrom str strs (f + 1) c st = some L) : L = [] := by
  rw [nodesFrom_end hd] at h
  cases h; rfl

/-- A walk that succeeds reads a token that `decodeToken` accepts first. -/
theorem nodesFrom_decode {f c : Nat} {st : List Nat} {L : List Begin}
    (h : nodesFrom str strs f c st = some L) :
    ∃ f' tok next, f = f' + 1 ∧ decodeToken str strs c = .ok (tok, next) := by
  cases f with
  | zero => cases h
  | succ f =>
    rw [nodesFrom] at h
    split at h
    all_goals first
      | exact ⟨f, _, _, rfl, ‹_›⟩
      | cases h

/-- A token that `decodeToken` reads starts with a tag that `u32At` reads. -/
theorem decodeToken_tag_ok {c next : Nat} {tok : Token}
    (h : decodeToken str strs c = .ok (tok, next)) : ∃ tag, u32At str c = .ok tag := by
  unfold decodeToken at h
  obtain ⟨tag, htag, -⟩ := except_bind_ok.1 h
  exact ⟨tag, htag⟩

/-- A begin-node token that `decodeToken` reads: its name lies after the tag,
followed by its NUL, and the next token lies at the next multiple of 4 after
the NUL, within the block. -/
theorem decodeToken_begin {c next : Nat} {nm : String}
    (h : decodeToken str strs c = .ok (.beginNode nm, next)) :
    next = align4 (c + 4 + nm.utf8ByteSize + 1) ∧
      str.extract (c + 4) (c + 4 + nm.utf8ByteSize) = nm.toByteArray ∧ next ≤ str.size := by
  unfold decodeToken at h
  obtain ⟨tag, -, h⟩ := except_bind_ok.1 h
  split at h
  · obtain ⟨⟨nm', e⟩, hcs, h⟩ := except_bind_ok.1 h
    obtain ⟨a, hpe, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    cases except_pure_ok.1 h
    obtain ⟨-, rfl⟩ := cString_nul hcs
    obtain ⟨rfl, hle⟩ := paddedEnd_ok hpe
    exact ⟨rfl, cString_extract hcs, hle⟩
  · cases except_pure_ok.1 h
  · obtain ⟨len, -, h⟩ := except_bind_ok.1 h
    obtain ⟨off, -, h⟩ := except_bind_ok.1 h
    obtain ⟨ve, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨⟨nm', e'⟩, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨a, -, h⟩ := except_bind_ok.1 h
    cases except_pure_ok.1 h
  · cases except_pure_ok.1 h
  · cases except_pure_ok.1 h
  · exact absurd h (except_throw_ne _ _)

/-- The cursor of every token lies after the one before. -/
theorem decodeToken_next_ge {c next : Nat} {tok : Token}
    (h : decodeToken str strs c = .ok (tok, next)) : c + 4 ≤ next := by
  unfold decodeToken at h
  obtain ⟨tag, -, h⟩ := except_bind_ok.1 h
  split at h
  · obtain ⟨⟨nm, e⟩, hcs, h⟩ := except_bind_ok.1 h
    obtain ⟨a, hpe, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    cases except_pure_ok.1 h
    obtain ⟨-, rfl⟩ := cString_nul hcs
    obtain ⟨rfl, -⟩ := paddedEnd_ok hpe
    have := le_align4 (c + 4 + nm.utf8ByteSize + 1)
    omega
  · cases except_pure_ok.1 h; omega
  · obtain ⟨len, -, h⟩ := except_bind_ok.1 h
    obtain ⟨off, -, h⟩ := except_bind_ok.1 h
    obtain ⟨ve, hve, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨⟨nm, e'⟩, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨a, hpe, h⟩ := except_bind_ok.1 h
    cases except_pure_ok.1 h
    obtain rfl := checkedAdd_ok hve
    obtain ⟨rfl, -⟩ := paddedEnd_ok hpe
    have := le_align4 (c + 4 + 8 + len.toNat)
    omega
  · cases except_pure_ok.1 h; omega
  · cases except_pure_ok.1 h; omega
  · exact absurd h (except_throw_ne _ _)

/-- The begin-node tokens of a walk lie at or after its cursor, each after the
one before, and are fewer than its fuel. -/
theorem nodesFrom_sorted : ∀ {f c : Nat} {st : List Nat} {L : List Begin},
    nodesFrom str strs f c st = some L →
      (∀ b ∈ L, c ≤ b.offset) ∧ L.Pairwise (fun a b => a.offset < b.offset) ∧ L.length < f
  | 0, _, _, _, h => by cases h
  | f + 1, c, st, L, h => by
    rw [nodesFrom] at h
    split at h
    · rename_i nm next hd
      have hn := decodeToken_next_ge hd
      split at h
      · obtain ⟨L', h', rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨h1, h2, h3⟩ := nodesFrom_sorted h'
        refine ⟨?_, ?_, by simp; omega⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact Nat.le_refl _
          · have := h1 b hb; omega
        · refine List.pairwise_cons.2 ⟨fun b hb => ?_, h2⟩
          have := h1 b hb; dsimp only; omega
      · cases h
    · rename_i next hd
      have hn := decodeToken_next_ge hd
      obtain ⟨h1, h2, h3⟩ := nodesFrom_sorted h
      exact ⟨fun b hb => by have := h1 b hb; omega, h2, by omega⟩
    · rename_i nm value next hd
      have hn := decodeToken_next_ge hd
      obtain ⟨h1, h2, h3⟩ := nodesFrom_sorted h
      exact ⟨fun b hb => by have := h1 b hb; omega, h2, by omega⟩
    · rename_i next hd
      have hn := decodeToken_next_ge hd
      obtain ⟨h1, h2, h3⟩ := nodesFrom_sorted h
      exact ⟨fun b hb => by have := h1 b hb; omega, h2, by omega⟩
    · cases h
      exact ⟨fun _ hb => absurd hb (List.not_mem_nil), List.Pairwise.nil, by simp⟩
    · cases h

/-- In begin-node tokens with increasing offsets, the first at the offset of
one of them is that one. -/
theorem find?_offset {L : List Begin} (hs : L.Pairwise (fun a b => a.offset < b.offset))
    {p : Nat} (hp : p < L.length) : L.find? (fun b => b.offset = L[p].offset) = some L[p] := by
  induction L generalizing p with
  | nil => cases hp
  | cons b L ih =>
    obtain ⟨hb, hL⟩ := List.pairwise_cons.1 hs
    cases p with
    | zero => simp
    | succ p =>
      have hp' : p < L.length := by simp at hp; omega
      have hlt : b.offset < L[p].offset := hb _ (List.getElem_mem hp')
      simp only [List.find?_cons, List.getElem_cons_succ]
      rw [show decide (b.offset = L[p].offset) = false by simp; omega]
      exact ih hL hp'

/-- Each begin-node token of a walk is one that `decodeToken` reads with its name. -/
theorem nodesFrom_mem : ∀ {f c : Nat} {st : List Nat} {L : List Begin},
    nodesFrom str strs f c st = some L →
      ∀ b ∈ L, ∃ next, decodeToken str strs b.offset = .ok (.beginNode b.name, next)
  | 0, _, _, _, h => by cases h
  | f + 1, c, st, L, h => by
    rw [nodesFrom] at h
    split at h
    · rename_i nm next hd
      split at h
      · obtain ⟨L', h', rfl⟩ := Option.map_eq_some_iff.1 h
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨next, hd⟩
        · exact nodesFrom_mem h' b hb
      · cases h
    · exact nodesFrom_mem h
    · exact nodesFrom_mem h
    · exact nodesFrom_mem h
    · cases h
      exact fun _ hb => absurd hb List.not_mem_nil
    · cases h

/-- Any function with the equations of `beginOffsets` of the statements gives
the offsets of the begin-node tokens of a walk that succeeds. -/
theorem offsets_of_nodesFrom (g : Nat → Nat → List Nat) (h0 : ∀ c, g 0 c = [])
    (hs : ∀ f c, g (f + 1) c =
      match decodeToken str strs c with
      | .ok (.beginNode _, next) => c :: g f next
      | .ok (.endStructure, _) => []
      | .ok (_, next) => g f next
      | .error _ => []) :
    ∀ {f c : Nat} {st : List Nat} {L : List Begin},
      nodesFrom str strs f c st = some L → g f c = L.map (·.offset)
  | 0, _, _, _, h => by cases h
  | f + 1, c, st, L, h => by
    rw [nodesFrom] at h
    rw [hs]
    split at h
    · rename_i nm next hd
      simp only [hd]
      split at h
      · obtain ⟨L', h', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [offsets_of_nodesFrom g h0 hs h']
        rfl
      · cases h
    · rename_i next hd
      simp only [hd]
      exact offsets_of_nodesFrom g h0 hs h
    · rename_i nm value next hd
      simp only [hd]
      exact offsets_of_nodesFrom g h0 hs h
    · rename_i next hd
      simp only [hd]
      exact offsets_of_nodesFrom g h0 hs h
    · rename_i next hd
      simp only [hd]
      cases h
      rfl
    · cases h


/-! ## The walk of the parse -/

/-- The begin-node tokens `L` stand for the records `recs`: as many, each with
the name of its record and, as its parent, the offset of the begin-node token
of the parent of its record. -/
def BeginsOf (recs : Array NodeRecord) (L : List Begin) : Prop :=
  L.length = recs.size ∧ ∀ i (h1 : i < L.length) (h2 : i < recs.size),
    L[i].name = recs[i].name ∧ L[i].parent = recs[i].parent.bind (fun p => L[p]?.map (·.offset))

/-- How the begin-node tokens `pre` read before a token and the offsets `st`
of the open nodes stand for the walk `w` of the parse at that token: `pre`
stands for its records, whose parents precede them, and `st` holds the
offsets of the begin-node tokens of its open nodes. -/
structure WalkRel (w : Walk) (pre : List Begin) (st : List Nat) : Prop where
  begins : BeginsOf w.records pre
  below : ∀ i (h : i < w.records.size) p, w.records[i].parent = some p → p < i
  stack : List.Forall₂ (fun off i => pre[i]?.map (·.offset) = some off) st (w.open_.map (·.index))

/-- A begin node that the walk places: the depth of the open nodes before it
is below `MAX_DEPTH`, and it opens a node with a new record. -/
theorem place_begin_eq {w w' : Walk} {nm : String} (h : w.place (.beginNode nm) = .ok w') :
    w.open_.length < MAX_DEPTH.toNat ∧ w'.records = w.records.push ⟨nm, w.open_.head?.map (·.index), []⟩ ∧
      w'.open_.map (·.index) = w.records.size :: w.open_.map (·.index) := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨h2, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    exact ⟨Nat.lt_of_not_le h2, rfl, rfl⟩
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨h2, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    exact ⟨Nat.lt_of_not_le h2, rfl, rfl⟩

/-- A property that the walk places changes only the properties of the record
of the innermost open node. -/
theorem place_property_eq {w w' : Walk} {nm : String} {v : ByteArray}
    (h : w.place (.property nm v) = .ok w') :
    ∃ k, w'.records = w.records.modify k (fun r => { r with properties := r.properties ++ [(nm, v)] }) ∧
      w'.open_.map (·.index) = w.open_.map (·.index) := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil => rw [Walk.place] at h; exact absurd h (except_throw_ne _ _)
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    have h := except_pure_ok.1 h
    subst h
    exact ⟨f.index, rfl, rfl⟩

/-- An end node that the walk places closes the innermost open node. -/
theorem place_endNode_eq {w w' : Walk} (h : w.place .endNode = .ok w') :
    w'.records = w.records ∧ w'.open_.map (·.index) = (w.open_.map (·.index)).tail := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil => cases h
  | cons f rest => cases h; exact ⟨rfl, rfl⟩

/-- Begin-node tokens of earlier records keep their offsets when more follow. -/
theorem getElem?_map_append {pre more : List Begin} {i off : Nat}
    (h : pre[i]?.map (·.offset) = some off) : (pre ++ more)[i]?.map (·.offset) = some off := by
  have hi : i < pre.length := by
    rcases Nat.lt_or_ge i pre.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at h; cases h
  rw [List.getElem?_append_left hi]; exact h

/-- A begin node keeps `WalkRel`, with its begin-node token read and opened. -/
theorem walkRel_begin {w w' : Walk} {pre : List Begin} {st : List Nat} {c : Nat} {nm : String}
    (hw : WalkRel w pre st) (h : w.place (.beginNode nm) = .ok w') :
    st.length < MAX_DEPTH.toNat ∧ WalkRel w' (pre ++ [⟨c, nm, st.head?⟩]) (c :: st) := by
  obtain ⟨hdepth, hrec, hop⟩ := place_begin_eq h
  obtain ⟨⟨hsz, hb⟩, hbelow, hst⟩ := hw
  obtain ⟨op', sr', recs'⟩ := w'
  dsimp only at hrec hop ⊢
  subst hrec
  have hlen : st.length = w.open_.length := by simpa using hst.length_eq
  have hhead : (w.open_.head?.map (·.index)).bind (fun p => (pre ++ [⟨c, nm, st.head?⟩])[p]?.map (·.offset)) =
      st.head? := by
    cases hs : w.open_ with
    | nil =>
      rw [hs] at hst
      cases hst; rfl
    | cons f rest =>
      rw [hs] at hst
      cases hst with
      | cons h1 _ =>
        simp only [List.head?_cons, Option.map_some, Option.bind_some]
        exact getElem?_map_append h1
  have hfr : ∀ p, w.open_.head?.map (·.index) = some p → p < w.records.size := by
    intro p hp
    cases hs : w.open_ with
    | nil => rw [hs] at hp; cases hp
    | cons f rest =>
      rw [hs] at hp hst
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hp
      subst hp
      simp only [List.map_cons] at hst
      cases hst with
      | cons h1 _ =>
        rcases Nat.lt_or_ge f.index pre.length with hi | hi
        · omega
        · rw [List.getElem?_eq_none hi] at h1; cases h1
  refine ⟨by omega, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · simp [hsz]
  · intro i h1 h2
    rcases Nat.lt_or_ge i w.records.size with hi | hi
    · have hi' : i < pre.length := by omega
      rw [List.getElem_append_left hi', Array.getElem_push_lt hi]
      obtain ⟨hn, hp⟩ := hb i hi' hi
      refine ⟨hn, ?_⟩
      rw [hp]
      cases hpar : w.records[i].parent with
      | none => rfl
      | some p =>
        have := hbelow i hi p hpar
        simp only [Option.bind_some]
        rw [List.getElem?_append_left (by omega)]
    · have hi' : i = pre.length := by simp at h2; omega
      subst hi'
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      simp only [hsz, Array.getElem_push_eq]
      exact ⟨trivial, hhead.symm⟩
  · intro i h p hp
    rcases Nat.lt_or_ge i w.records.size with hi | hi
    · rw [Array.getElem_push_lt hi] at hp; exact hbelow i hi p hp
    · have hi' : i = w.records.size := by simp at h; omega
      subst hi'
      rw [Array.getElem_push_eq] at hp
      exact hfr p hp
  · rw [hop]
    refine List.Forall₂.cons ?_ ?_
    · rw [← hsz, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    · exact hst.imp fun _ _ h => getElem?_map_append h

/-- A property keeps `WalkRel`. -/
theorem walkRel_property {w w' : Walk} {pre : List Begin} {st : List Nat} {nm : String}
    {v : ByteArray} (hw : WalkRel w pre st) (h : w.place (.property nm v) = .ok w') :
    WalkRel w' pre st := by
  obtain ⟨k, hrec, hop⟩ := place_property_eq h
  obtain ⟨⟨hsz, hb⟩, hbelow, hst⟩ := hw
  have hg : ∀ i (hi : i < w.records.size) (hi' : i < w'.records.size),
      w'.records[i].name = w.records[i].name ∧ w'.records[i].parent = w.records[i].parent := by
    intro i hi hi'
    simp only [hrec, Array.getElem_modify]
    split <;> exact ⟨rfl, rfl⟩
  have hs : w'.records.size = w.records.size := by rw [hrec]; simp
  refine ⟨⟨by omega, fun i h1 h2 => ?_⟩, fun i h p hp => ?_, by rw [hop]; exact hst⟩
  · obtain ⟨e1, e2⟩ := hg i (by omega) h2
    rw [e1, e2]; exact hb i h1 (by omega)
  · rw [(hg i (by omega) h).2] at hp
    exact hbelow i (by omega) p hp

/-- An end node keeps `WalkRel`, with the innermost open node closed. -/
theorem walkRel_endNode {w w' : Walk} {pre : List Begin} {st : List Nat}
    (hw : WalkRel w pre st) (h : w.place .endNode = .ok w') : WalkRel w' pre st.tail := by
  obtain ⟨hrec, hop⟩ := place_endNode_eq h
  obtain ⟨hb, hbelow, hst⟩ := hw
  refine ⟨hrec ▸ hb, hrec ▸ hbelow, ?_⟩
  rw [hop]
  generalize w.open_.map (·.index) = l at hst
  cases hst with
  | nil => exact List.Forall₂.nil
  | cons _ h => exact h

/-- The walk that succeeds from a state that `WalkRel` relates to the
begin-node tokens `pre` and the offsets `st`: the walk of `nodesFrom` succeeds
on the same tokens, and with `pre` before them its begin-node tokens stand for
the records of the parse. -/
theorem nodesFrom_walkTokens : ∀ {f c : Nat} {w : Walk} {pre : List Begin} {st : List Nat}
    {recs : Array NodeRecord}, WalkRel w pre st → walkTokens str strs f c w = .ok recs →
      ∃ L, nodesFrom str strs f c st = some L ∧ BeginsOf recs (pre ++ L)
  | 0, _, _, _, _, _, _, h => by cases h
  | f + 1, c, w, pre, st, recs, hw, h => by
    rw [walkTokens] at h
    obtain ⟨⟨tok, next⟩, hd, h⟩ := except_bind_ok.1 h
    cases tok with
    | endStructure =>
      obtain ⟨-, h⟩ := except_jp_ok h
      cases except_pure_ok.1 h
      exact ⟨[], nodesFrom_end hd, by simpa using hw.begins⟩
    | beginNode nm =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hdepth, hw'⟩ := walkRel_begin (c := c) hw hp
      obtain ⟨L, hL, hb⟩ := nodesFrom_walkTokens hw' h
      refine ⟨⟨c, nm, st.head?⟩ :: L, ?_, by simpa using hb⟩
      rw [nodesFrom_begin hd]
      simp only [hdepth, ↓reduceIte, hL, Option.map_some]
    | property nm v =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨L, hL, hb⟩ := nodesFrom_walkTokens (walkRel_property hw hp) h
      exact ⟨L, by rw [nodesFrom_property hd, hL], hb⟩
    | endNode =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨L, hL, hb⟩ := nodesFrom_walkTokens (walkRel_endNode hw hp) h
      exact ⟨L, by rw [nodesFrom_endNode hd, hL], hb⟩
    | nop =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      cases hp
      obtain ⟨L, hL, hb⟩ := nodesFrom_walkTokens hw h
      exact ⟨L, by rw [nodesFrom_nop hd, hL], hb⟩

/-- The walk before the first token. -/
theorem walkRel_start : WalkRel Walk.start [] [] :=
  ⟨⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ h => absurd h (Nat.not_lt_zero _),
    List.Forall₂.nil⟩

/-- The structure block of a tree that the parse accepts: the walk of
`nodesFrom` from its first token succeeds, and its begin-node tokens stand for
the records of the tree. -/
theorem parse_nodesFrom {input : ByteArray} {T : Fdt} {h : Header}
    (hp : Fdt.parse input = .ok T) (hh : header input = .ok h) :
    ∃ L, nodesFrom h.structure_ h.strings MAX_TOKENS.toNat 0 [] = some L ∧ BeginsOf T.records L := by
  unfold Fdt.parse at hp
  obtain ⟨h', hh', hp⟩ := except_bind_ok.1 hp
  rw [hh] at hh'
  cases hh'
  obtain ⟨res, -, hp⟩ := except_bind_ok.1 hp
  obtain ⟨recs, hr, hp⟩ := except_bind_ok.1 hp
  cases except_pure_ok.1 hp
  obtain ⟨L, hL, hb⟩ := nodesFrom_walkTokens walkRel_start hr
  exact ⟨L, hL, by simpa using hb⟩

end NodesFrom

/-! ## The nodes of a tree -/

theorem nodes_length (T : Fdt) : T.nodes.length = T.records.size := by
  simp [Fdt.nodes]

theorem nodes_getElem (T : Fdt) (k : Nat) (hk : k < T.nodes.length) :
    T.nodes[k] = ⟨T, ⟨k, by rwa [nodes_length] at hk⟩⟩ := by
  simp [Fdt.nodes]

/-- The nodes from index `k` on, when there is one: the node of index `k`, then
those from `k + 1` on. -/
theorem nodes_drop_cons {T : Fdt} {k : Nat} {b : Node} {l : List Node}
    (h : b :: l = T.nodes.drop k) :
    ∃ hk : k < T.records.size, b = ⟨T, ⟨k, hk⟩⟩ ∧ l = T.nodes.drop (k + 1) := by
  have hk : k < T.nodes.length := by
    rcases Nat.lt_or_ge k T.nodes.length with hk | hk
    · exact hk
    · rw [List.drop_of_length_le hk] at h; cases h
  rw [List.drop_eq_getElem_cons hk, nodes_getElem] at h
  obtain ⟨rfl, rfl⟩ := List.cons.inj h
  exact ⟨by rwa [nodes_length] at hk, rfl, rfl⟩

/-- No node from index `k` on. -/
theorem nodes_drop_nil {T : Fdt} {k : Nat} (h : [] = T.nodes.drop k) : T.records.size ≤ k := by
  have := congrArg List.length h
  simp only [List.length_nil, List.length_drop, nodes_length] at this
  omega

/-! ## The blocks of a header -/

/-- A block lies within the bytes of the tree. -/
theorem block_size_le {blob b : ByteArray} {start size : Nat} (h : block blob start size = .ok b) :
    b.size ≤ blob.size := by
  unfold block at h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨e, he, h⟩ := except_bind_ok.1 h
  obtain ⟨h2, h⟩ := except_jp_ok h
  cases except_pure_ok.1 h
  rw [ByteArray.size_extract]
  omega

/-- The bytes of a tree that the header accepts are at most `MAX_BLOB_SIZE`,
and its blocks lie within them. -/
theorem header_sizes {input : ByteArray} {hd : Header} (h : header input = .ok hd) :
    hd.blob.size ≤ MAX_BLOB_SIZE.toNat ∧ hd.structure_.size ≤ hd.blob.size ∧
      hd.strings.size ≤ hd.blob.size := by
  unfold header at h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨m, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨v, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨h4, h⟩ := except_jp_ok h
  obtain ⟨h5, h⟩ := except_jp_ok h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨b1, hb1, h⟩ := except_bind_ok.1 h
  obtain ⟨b2, hb2, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  have h := except_pure_ok.1 h
  subst h
  refine ⟨?_, block_size_le hb1, block_size_le hb2⟩
  rw [ByteArray.size_extract]
  omega

end Krepi.Proofs.Fdt.Refinement

module

public import Krepi.Proofs.Fdt.Refinement.Utf8Lemmas
public import Krepi.Spec.Fdt.Nodes
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.PathLemmas

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
- The properties of the records: `propsFrom`, the properties from a cursor up
  to the next begin node, end node or end token, as `property_range` walks
  them (`propsFrom_zero`, `propsFrom_property`, `propsFrom_nop`,
  `propsFrom_end`); `WalkProp` (the open nodes lie among the records, and only
  the innermost may have no child yet) and `Unchildren` (a record that may
  still take properties), with `walkProp_start`, `place_begin_full`,
  `place_property_full`, `place_endNode_full`, `walkProp_begin`,
  `walkProp_property`, `walkProp_endNode` and `not_unchildren_of_tail`;
  `props_walkTokens` (a record that may take no more properties keeps its
  own, the innermost one gets those that `propsFrom` reads from the cursor),
  `props_walk` and `parse_props`: the properties of each record of a tree
  that the parse accepts are those that `propsFrom` reads after the
  begin-node token of the record, within `MAX_TOKENS` tokens.
- The nodes of a tree: `nodes_length`, `nodes_getElem`, `nodes_drop_cons`
  and `nodes_drop_nil`.
- The header: `block_size_le` and `header_sizes` (the bytes of a tree are at
  most `MAX_BLOB_SIZE`, its blocks within them).
- Paths as bytes: `utf8Bytes`, the bytes of the UTF-8 encoding of characters
  (`utf8Bytes_nil`, `utf8Bytes_cons`, `utf8Bytes_append`, `toUTF8_toList`,
  `utf8Bytes_inj`, `utf8Bytes_eq_nil`), with `enc_slash`, `mem_enc_slash`
  (the byte 47 lies in the encoding of `/` alone), `ne_or_high`,
  `enc_ne_nil` and `head_enc_ne`; `doubleSlashB`, `pathValidB` and `splitB`,
  the checks and the split of `Fdt.findNode` on bytes as the code reads them,
  equal to those of the characters (`doubleSlashB_utf8`, `pathValidB_utf8`,
  `splitB_utf8`), with their steps (`doubleSlashB_cons_of_ne`,
  `doubleSlashB_append`, `doubleSlashB_slash`, `doubleSlashB_drop`,
  `doubleSlashB_drop'`, `doubleSlashB_short`, `getLast_utf8`,
  `length_utf8_gt`, `splitB_ne_nil`, `splitB_append_of` and `splitB_at`, the
  split at the first `/` from an index).
- The lookup of a path on bytes: `scanChild`, the search of `child_named`
  among the nodes in their order (`scanChild_some`, `scanChild_none`, against
  the filter of `Fdt.descend`), `childPred`, `descendB` (`Fdt.descend` on
  components as bytes, `childPred_utf8`, `descendB_utf8`) and `findNode_eq`
  (`Fdt.findNode` on the bytes of the path); `offset_inj` and
  `parent_offset_iff` (the token of a record has the offset of the token of
  `p` as its parent exactly when `p` is the parent of the record).
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

/-! ## The properties of the records -/

section Props

variable {str strs : ByteArray}

/-- The properties from the token at `cursor` on, reading at most `fuel`
tokens as `decodeToken` reads them, as `property_range` walks them: each
property with its name and value, no-operations skipped, up to the first begin
node, end node or end token; none when a token is refused or the fuel runs
out. -/
def propsFrom (str strs : ByteArray) : (fuel cursor : Nat) → Option (List (String × ByteArray))
  | 0, _ => none
  | fuel + 1, cursor =>
    match decodeToken str strs cursor with
    | .ok (.property nm v, next) => (propsFrom str strs fuel next).map ((nm, v) :: ·)
    | .ok (.nop, next) => propsFrom str strs fuel next
    | .ok (.beginNode _, _) => some []
    | .ok (.endNode, _) => some []
    | .ok (.endStructure, _) => some []
    | .error _ => none

/-- The open nodes of a walk lie among its records, and every open node but the
innermost has a child. -/
def WalkProp (w : Walk) : Prop :=
  (∀ fr ∈ w.open_, fr.index < w.records.size) ∧ ∀ fr ∈ w.open_.tail, fr.children = true

/-- The record `k` is that of the innermost open node, which has no child yet:
properties may still follow for it. -/
def Unchildren (w : Walk) (k : Nat) : Prop :=
  ∃ fr rest, w.open_ = fr :: rest ∧ fr.children = false ∧ fr.index = k

theorem walkProp_start : WalkProp Walk.start := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- A begin node that the walk places: the records and open nodes after it. -/
theorem place_begin_full {w w' : Walk} {nm : String} (h : w.place (.beginNode nm) = .ok w') :
    w'.records = w.records.push ⟨nm, w.open_.head?.map (·.index), []⟩ ∧
      w'.open_ = ⟨w.records.size, [], false⟩ :: (match w.open_ with
        | [] => []
        | f :: rest => { f with children := true } :: rest) := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    exact ⟨rfl, rfl⟩
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    exact ⟨rfl, rfl⟩

/-- A property that the walk places: it belongs to the innermost open node,
which has no child. -/
theorem place_property_full {w w' : Walk} {nm : String} {v : ByteArray}
    (h : w.place (.property nm v) = .ok w') :
    ∃ f rest, w.open_ = f :: rest ∧ f.children = false ∧
      w'.records = w.records.modify f.index (fun r => { r with properties := r.properties ++ [(nm, v)] }) ∧
      w'.open_ = { f with names := f.names ++ [nm] } :: rest := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil => rw [Walk.place] at h; exact absurd h (except_throw_ne _ _)
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨h1, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    have h := except_pure_ok.1 h
    subst h
    exact ⟨f, rest, rfl, by simpa using h1, rfl, rfl⟩

/-- An end node that the walk places closes the innermost open node. -/
theorem place_endNode_full {w w' : Walk} (h : w.place .endNode = .ok w') :
    w'.records = w.records ∧ ∃ f, w.open_ = f :: w'.open_ := by
  obtain ⟨op, sr, recs⟩ := w
  cases op with
  | nil => cases h
  | cons f rest => cases h; exact ⟨rfl, f, rfl⟩

theorem propsFrom_zero (c : Nat) : propsFrom str strs 0 c = none := rfl

theorem propsFrom_property {f c next : Nat} {nm : String} {v : ByteArray}
    (hd : decodeToken str strs c = .ok (.property nm v, next)) :
    propsFrom str strs (f + 1) c = (propsFrom str strs f next).map ((nm, v) :: ·) := by
  rw [propsFrom, hd]

theorem propsFrom_nop {f c next : Nat} (hd : decodeToken str strs c = .ok (.nop, next)) :
    propsFrom str strs (f + 1) c = propsFrom str strs f next := by
  rw [propsFrom, hd]

theorem propsFrom_end {f c next : Nat} {tok : Token}
    (hd : decodeToken str strs c = .ok (tok, next))
    (ht : tok = .endStructure ∨ tok = .endNode ∨ ∃ nm, tok = .beginNode nm) :
    propsFrom str strs (f + 1) c = some [] := by
  rcases ht with rfl | rfl | ⟨nm, rfl⟩ <;> rw [propsFrom, hd]

theorem not_unchildren_of_tail {w : Walk} (h : ∀ fr ∈ w.open_, fr.children = true) (k : Nat) :
    ¬ Unchildren w k := by
  rintro ⟨fr, rest, hs, hc, -⟩
  have := h fr (by rw [hs]; exact List.mem_cons_self)
  rw [hc] at this; cases this


theorem walkProp_begin {w w' : Walk} {nm : String} (hw : WalkProp w)
    (hp : w.place (.beginNode nm) = .ok w') : WalkProp w' := by
  obtain ⟨hrec, hop⟩ := place_begin_full hp
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun fr hfr => ?_, fun fr hfr => ?_⟩
  · rw [hrec, Array.size_push]
    rw [hop] at hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · exact Nat.lt_succ_self _
    · cases hs : w.open_ with
      | nil => rw [hs] at hfr; cases hfr
      | cons f0 rest =>
        rw [hs] at hfr
        rcases List.mem_cons.1 hfr with rfl | hfr
        · have := h1 f0 (by rw [hs]; exact List.mem_cons_self); exact Nat.lt_succ_of_lt this
        · have := h1 fr (by rw [hs]; exact List.mem_cons_of_mem _ hfr)
          exact Nat.lt_succ_of_lt this
  · rw [hop, List.tail_cons] at hfr
    cases hs : w.open_ with
    | nil => rw [hs] at hfr; cases hfr
    | cons f0 rest =>
      rw [hs] at hfr
      rcases List.mem_cons.1 hfr with rfl | hfr
      · rfl
      · exact h2 fr (by rw [hs]; exact hfr)

theorem walkProp_property {w w' : Walk} {nm : String} {v : ByteArray} (hw : WalkProp w)
    (hp : w.place (.property nm v) = .ok w') : WalkProp w' := by
  obtain ⟨f0, rest0, hs0, hc0, hrec, hop⟩ := place_property_full hp
  have hsz : w'.records.size = w.records.size := by rw [hrec]; simp
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun fr hfr => ?_, fun fr hfr => ?_⟩
  · rw [hsz]
    rw [hop] at hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · exact h1 f0 (by rw [hs0]; exact List.mem_cons_self)
    · exact h1 fr (by rw [hs0]; exact List.mem_cons_of_mem _ hfr)
  · rw [hop, List.tail_cons] at hfr
    exact h2 fr (by rw [hs0]; exact hfr)

theorem walkProp_endNode {w w' : Walk} (hw : WalkProp w) (hp : w.place .endNode = .ok w') :
    WalkProp w' := by
  obtain ⟨hrec, f0, hs0⟩ := place_endNode_full hp
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun fr hfr => ?_, fun fr hfr => ?_⟩
  · rw [hrec]; exact h1 fr (by rw [hs0]; exact List.mem_cons_of_mem _ hfr)
  · exact h2 fr (by rw [hs0]; exact List.mem_of_mem_tail hfr)

/-- The properties that a walk that succeeds gives its records: a record that
can take no more properties keeps its own, and that of the innermost open
node, without a child, gets those from the cursor on, as `propsFrom` reads
them. -/
theorem props_walkTokens : ∀ {f c : Nat} {w : Walk} {recs : Array NodeRecord},
    WalkProp w → walkTokens str strs f c w = .ok recs →
    (∀ k (hk : k < w.records.size), ¬ Unchildren w k →
      recs[k]?.map (·.properties) = some w.records[k].properties) ∧
    (∀ fr rest, w.open_ = fr :: rest → fr.children = false →
      ∃ ps, propsFrom str strs f c = some ps ∧
        recs[fr.index]?.map (·.properties) = w.records[fr.index]?.map (·.properties ++ ps))
  | 0, _, _, _, _, h => by cases h
  | f + 1, c, w, recs, hw, h => by
    rw [walkTokens] at h
    obtain ⟨⟨tok, next⟩, hd, h⟩ := except_bind_ok.1 h
    cases tok with
    | endStructure =>
      obtain ⟨-, h⟩ := except_jp_ok h
      cases except_pure_ok.1 h
      refine ⟨fun k hk _ => by simp [hk], fun fr rest _ _ => ⟨[], propsFrom_end hd (Or.inl rfl), ?_⟩⟩
      simp
    | beginNode nm =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hrec, hop⟩ := place_begin_full hp
      have hw' := walkProp_begin hw hp
      obtain ⟨hA, -⟩ := props_walkTokens hw' h
      have hnot : ∀ k, k < w.records.size → ¬ Unchildren w' k := by
        rintro k hk ⟨fr, rest, hs, -, hi⟩
        rw [hop] at hs
        obtain ⟨rfl, -⟩ := List.cons.inj hs
        simp at hi; omega
      refine ⟨fun k hk _ => ?_, fun fr rest hs hc => ⟨[], propsFrom_end hd (Or.inr (Or.inr ⟨nm, rfl⟩)), ?_⟩⟩
      · have := hA k (by rw [hrec]; simp; omega) (hnot k hk)
        rw [this]; simp only [hrec, Array.getElem_push_lt hk]
      · have hi : fr.index < w.records.size := hw.1 fr (by rw [hs]; exact List.mem_cons_self)
        have := hA fr.index (by rw [hrec]; simp; omega) (hnot _ hi)
        rw [this]; simp only [hrec, Array.getElem_push_lt hi, List.append_nil]
        rw [Array.getElem?_eq_getElem hi]; rfl
    | property nm v =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨f0, rest0, hs0, hc0, hrec, hop⟩ := place_property_full hp
      have hsz : w'.records.size = w.records.size := by rw [hrec]; simp
      have hw' := walkProp_property hw hp
      obtain ⟨hA, hB⟩ := props_walkTokens hw' h
      refine ⟨fun k hk hk' => ?_, fun fr rest hs hc => ?_⟩
      · have hne : k ≠ f0.index := fun e => hk' ⟨f0, rest0, hs0, hc0, e.symm⟩
        have hnot : ¬ Unchildren w' k := by
          rintro ⟨fr, rest, hs, -, hi⟩
          rw [hop] at hs
          obtain ⟨rfl, -⟩ := List.cons.inj hs
          exact hne hi.symm
        rw [hA k (by omega) hnot]
        simp only [hrec, Array.getElem_modify, Ne.symm hne, ↓reduceIte]
      · rw [hs0] at hs
        obtain ⟨hfr, -⟩ := List.cons.inj hs
        rw [← hfr]
        obtain ⟨ps, hps, hrecs⟩ := hB _ rest0 hop hc0
        refine ⟨(nm, v) :: ps, by rw [propsFrom, hd]; simp only [hps]; rfl, ?_⟩
        rw [hrecs]
        have hi : f0.index < w.records.size := hw.1 f0 (by rw [hs0]; exact List.mem_cons_self)
        simp only [hrec, Array.getElem?_modify, Array.getElem?_eq_getElem hi]
        simp
    | endNode =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hrec, f0, hs0⟩ := place_endNode_full hp
      have hw' := walkProp_endNode hw hp
      obtain ⟨hA, -⟩ := props_walkTokens hw' h
      have hnot : ∀ k, ¬ Unchildren w' k :=
        not_unchildren_of_tail (fun fr hfr => hw.2 fr (by rw [hs0]; exact hfr))
      refine ⟨fun k hk _ => ?_, fun fr rest hs hc => ⟨[], propsFrom_end hd (Or.inr (Or.inl rfl)), ?_⟩⟩
      · rw [hA k (by rw [hrec]; exact hk) (hnot k)]; simp only [hrec]
      · have hi : fr.index < w.records.size := hw.1 fr (by rw [hs]; exact List.mem_cons_self)
        rw [hA fr.index (by rw [hrec]; exact hi) (hnot _)]
        simp only [hrec, Array.getElem?_eq_getElem hi, List.append_nil]; rfl
    | nop =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      cases hp
      obtain ⟨hA, hB⟩ := props_walkTokens hw h
      refine ⟨hA, fun fr rest hs hc => ?_⟩
      obtain ⟨ps, hps, hrecs⟩ := hB fr rest hs hc
      exact ⟨ps, by rw [propsFrom, hd]; exact hps, hrecs⟩

/-- The properties of each record that a walk that succeeds begins: those
that `propsFrom` reads after its begin-node token, within the fuel. -/
theorem props_walk : ∀ {f c : Nat} {w : Walk} {pre : List Begin} {st : List Nat}
    {recs : Array NodeRecord} {more : List Begin},
    WalkRel w pre st → WalkProp w → walkTokens str strs f c w = .ok recs →
    nodesFrom str strs f c st = some more →
    ∀ k, pre.length ≤ k → ∀ (hk2 : k < (pre ++ more).length) (hk3 : k < recs.size),
      ∃ f' ≤ f, propsFrom str strs f' (align4 ((pre ++ more)[k].offset + 4 +
        (pre ++ more)[k].name.utf8ByteSize + 1)) = some recs[k].properties
  | 0, _, _, _, _, _, _, _, _, h, _ => by cases h
  | f + 1, c, w, pre, st, recs, more, hw, hwp, h, hn => by
    rw [walkTokens] at h
    obtain ⟨⟨tok, next⟩, hd, h⟩ := except_bind_ok.1 h
    cases tok with
    | endStructure =>
      cases nodesFrom_end_some hd hn
      intro k hk1 hk2; simp at hk2; omega
    | beginNode nm =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨-, more', rfl, hn'⟩ := nodesFrom_begin_some hd hn
      obtain ⟨-, hw'⟩ := walkRel_begin (c := c) hw hp
      obtain ⟨hrec, hop⟩ := place_begin_full hp
      have hwp' := walkProp_begin hwp hp
      intro k hk1 hk2 hk3
      rcases Nat.lt_or_ge pre.length k with hlt | hge
      · have := props_walk hw' hwp' h hn' k (by simp; omega) (by simpa using hk2) hk3
        obtain ⟨f', hf', hpf⟩ := this
        refine ⟨f', by omega, ?_⟩
        simpa using hpf
      · have hk : k = pre.length := Nat.le_antisymm hge hk1
        subst hk
        obtain ⟨-, hB⟩ := props_walkTokens hwp' h
        obtain ⟨ps, hps, hrecs⟩ := hB _ _ hop rfl
        obtain ⟨hnext, -, -⟩ := decodeToken_begin hd
        refine ⟨f, by omega, ?_⟩
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
        rw [← hnext, hps]
        dsimp only at hrecs
        rw [hrec, Array.getElem?_push_size, Option.map_some, List.nil_append] at hrecs
        have hsz : w.records.size = pre.length := hw.begins.1.symm
        rw [hsz, Array.getElem?_eq_getElem hk3, Option.map_some, Option.some.injEq] at hrecs
        rw [hrecs]
    | property nm v =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      rw [nodesFrom_property hd] at hn
      intro k hk1 hk2 hk3
      obtain ⟨f', hf', hpf⟩ := props_walk (walkRel_property hw hp) (walkProp_property hwp hp) h hn k
        hk1 hk2 hk3
      exact ⟨f', by omega, hpf⟩
    | endNode =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      rw [nodesFrom_endNode hd] at hn
      intro k hk1 hk2 hk3
      obtain ⟨f', hf', hpf⟩ := props_walk (walkRel_endNode hw hp) (walkProp_endNode hwp hp) h hn k
        hk1 hk2 hk3
      exact ⟨f', by omega, hpf⟩
    | nop =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      cases hp
      rw [nodesFrom_nop hd] at hn
      intro k hk1 hk2 hk3
      obtain ⟨f', hf', hpf⟩ := props_walk hw hwp h hn k hk1 hk2 hk3
      exact ⟨f', by omega, hpf⟩

/-- The properties of each record of a tree that the parse accepts: those that
`propsFrom` reads after the begin-node token of the record, within
`MAX_TOKENS` tokens. -/
theorem parse_props {input : ByteArray} {T : Fdt} {h : Header}
    (hp : Fdt.parse input = .ok T) (hh : header input = .ok h) {L : List Begin}
    (hL : nodesFrom h.structure_ h.strings MAX_TOKENS.toNat 0 [] = some L) :
    ∀ k (hk : k < L.length) (hk' : k < T.records.size), ∃ f ≤ MAX_TOKENS.toNat,
      propsFrom h.structure_ h.strings f (align4 (L[k].offset + 4 + L[k].name.utf8ByteSize + 1)) =
        some T.records[k].properties := by
  unfold Fdt.parse at hp
  obtain ⟨h', hh', hp⟩ := except_bind_ok.1 hp
  rw [hh] at hh'
  cases hh'
  obtain ⟨res, -, hp⟩ := except_bind_ok.1 hp
  obtain ⟨recs, hr, hp⟩ := except_bind_ok.1 hp
  cases except_pure_ok.1 hp
  intro k hk hk'
  have := props_walk walkRel_start walkProp_start hr hL k (Nat.zero_le _) (by simpa using hk) hk'
  simpa using this

end Props

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


/-! ## Paths as bytes -/

/-- The bytes of the UTF-8 encoding of characters. -/
def utf8Bytes (cs : List Char) : List UInt8 := cs.flatMap String.utf8EncodeChar

theorem utf8Bytes_nil : utf8Bytes [] = [] := rfl

theorem utf8Bytes_cons (c : Char) (cs : List Char) :
    utf8Bytes (c :: cs) = String.utf8EncodeChar c ++ utf8Bytes cs := List.flatMap_cons

theorem utf8Bytes_append (a b : List Char) : utf8Bytes (a ++ b) = utf8Bytes a ++ utf8Bytes b :=
  List.flatMap_append

theorem toUTF8_toList (s : String) : s.toUTF8.toList = utf8Bytes s.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, List.utf8Encode, toList_eq_data,
    List.data_toByteArray]
  rfl

theorem utf8Bytes_inj {a b : List Char} (h : utf8Bytes a = utf8Bytes b) : a = b := by
  have : (String.ofList a).toByteArray = (String.ofList b).toByteArray := by
    rw [String.toByteArray_ofList, String.toByteArray_ofList, List.utf8Encode, List.utf8Encode]
    exact congrArg List.toByteArray h
  rw [String.toByteArray_inj] at this
  rw [← String.toList_ofList (l := a), this, String.toList_ofList]

theorem enc_slash : String.utf8EncodeChar '/' = [47] := by
  rw [String.utf8EncodeChar_eq_utf8EncodeCharFast]; rfl

theorem or_ge {a b : UInt8} : b.toNat ≤ (a ||| b).toNat := by
  rw [UInt8.toNat_or]; exact Nat.right_le_or

theorem ne_or_high {x k : UInt8} (hk : 128 ≤ k.toNat) : (47 : UInt8) ≠ x ||| k := by
  intro h
  have := congrArg UInt8.toNat h
  have h2 : k.toNat ≤ (x ||| k).toNat := by rw [UInt8.toNat_or]; exact Nat.right_le_or
  rw [← this] at h2
  simp at h2
  omega

theorem mem_enc_slash {c : Char} (h : (47 : UInt8) ∈ String.utf8EncodeChar c) : c = '/' := by
  rw [String.utf8EncodeChar_eq_utf8EncodeCharFast] at h
  unfold String.utf8EncodeCharFast at h
  dsimp only at h
  split at h
  · rename_i hv
    simp only [List.mem_singleton] at h
    apply Char.ext
    have h1 := congrArg UInt8.toNat h
    have h2 : c.val.toNat ≤ 127 := by
      have := UInt32.le_iff_toNat_le.1 hv; simpa using this
    simp only [UInt32.toNat_toUInt8, UInt8.reduceToNat] at h1
    apply UInt32.toNat_inj.1
    simp only [show ('/' : Char).val.toNat = 47 from rfl]
    omega
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> exact absurd h (ne_or_high (by decide))
    · split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> exact absurd h (ne_or_high (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h <;> exact absurd h (ne_or_high (by decide))

theorem enc_ne_nil (c : Char) : String.utf8EncodeChar c ≠ [] := String.utf8EncodeChar_ne_nil

theorem utf8Bytes_eq_nil {cs : List Char} : utf8Bytes cs = [] ↔ cs = [] := by
  cases cs with
  | nil => simp [utf8Bytes]
  | cons c cs => simp [utf8Bytes_cons]

/-- Whether bytes hold two `/` in a row. -/
def doubleSlashB : List UInt8 → Bool
  | a :: b :: rest => (a == 47 && b == 47) || doubleSlashB (b :: rest)
  | _ => false

theorem doubleSlashB_cons_of_ne {x : UInt8} (hx : x ≠ 47) (Y : List UInt8) :
    doubleSlashB (x :: Y) = doubleSlashB Y := by
  cases Y with
  | nil => rfl
  | cons y Y => simp [doubleSlashB, hx]

theorem doubleSlashB_append {X Y : List UInt8} (hX : (47 : UInt8) ∉ X) :
    doubleSlashB (X ++ Y) = doubleSlashB Y := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    simp only [List.mem_cons, not_or] at hX
    rw [List.cons_append, doubleSlashB_cons_of_ne (Ne.symm hX.1), ih hX.2]

theorem doubleSlashB_slash (Y : List UInt8) :
    doubleSlashB (47 :: Y) = (Y.head? == some 47 || doubleSlashB Y) := by
  cases Y with
  | nil => rfl
  | cons y Y => simp [doubleSlashB]

theorem head_enc_ne {c : Char} (hc : c ≠ '/') :
    ∃ e es, String.utf8EncodeChar c = e :: es ∧ e ≠ 47 := by
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (enc_ne_nil c)
  refine ⟨e, es, he, fun h => hc (mem_enc_slash ?_)⟩
  rw [he, h]; exact List.mem_cons_self

/-- One step of `doubleSlashB` over the bytes from `i` on. -/
theorem doubleSlashB_drop {P : List UInt8} {i : Nat} (h : i + 1 < P.length) :
    doubleSlashB (P.drop i) =
      ((P[i] == 47 && P[i + 1] == 47) || doubleSlashB (P.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h, doubleSlashB]

/-- One step of `doubleSlashB` over the bytes from `j` on, with `i = j + 1`. -/
theorem doubleSlashB_drop' {P : List UInt8} {j i : Nat} (hji : j + 1 = i) (h : i < P.length) :
    doubleSlashB (P.drop j) =
      ((P[j] == 47 && P[i] == 47) || doubleSlashB (P.drop i)) := by
  subst hji; exact doubleSlashB_drop h

/-- At most one byte holds no `//`. -/
theorem doubleSlashB_short {P : List UInt8} (h : P.length ≤ 1) : doubleSlashB P = false := by
  match P, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem doubleSlashB_utf8 : ∀ cs : List Char, doubleSlashB (utf8Bytes cs) = hasDoubleSlash cs
  | [] => rfl
  | c :: cs => by
    by_cases hc : c = '/'
    · subst hc
      rw [utf8Bytes_cons, enc_slash, List.singleton_append, doubleSlashB_slash, doubleSlashB_utf8 cs]
      cases cs with
      | nil => rfl
      | cons d ds =>
        by_cases hd : d = '/'
        · subst hd; rw [utf8Bytes_cons, enc_slash]; rfl
        · obtain ⟨e, es, he, hne⟩ := head_enc_ne hd
          rw [utf8Bytes_cons, he]
          simp [hasDoubleSlash, hd, hne]
    · rw [utf8Bytes_cons, doubleSlashB_append (fun h => hc (mem_enc_slash h)), doubleSlashB_utf8 cs,
        hasDoubleSlash_cons hc]

/-- The form of a path that `path_valid` checks, on its bytes: a `/` first, no
`/` last but in the root, and no `//`. -/
def pathValidB (P : List UInt8) : Bool :=
  P.head? == some 47 && !(1 < P.length && P.getLast? == some 47) && !doubleSlashB P

theorem getLast_utf8 {cs : List Char} (hcs : cs ≠ []) :
    ((utf8Bytes cs).getLast? == some 47) = (cs.getLast? == some '/') := by
  obtain ⟨cs', d, rfl⟩ := List.eq_nil_or_concat cs |>.resolve_left hcs
  rw [List.concat_eq_append, utf8Bytes_append, utf8Bytes_cons, utf8Bytes_nil, List.append_nil,
    List.getLast?_append, List.getLast?_concat]
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (enc_ne_nil d)
  have hl : (String.utf8EncodeChar d).getLast? = some ((String.utf8EncodeChar d).getLast (enc_ne_nil d)) :=
    List.getLast?_eq_some_getLast _
  rw [hl, Option.some_or]
  by_cases hd : d = '/'
  · subst hd; simp [enc_slash]
  · have : (String.utf8EncodeChar d).getLast (enc_ne_nil d) ≠ 47 := fun h =>
      hd (mem_enc_slash (h ▸ List.getLast_mem _))
    simp [this, hd]

theorem length_utf8_gt {rest : List Char} :
    (1 < (utf8Bytes ('/' :: rest)).length) = (1 < ('/' :: rest).length) := by
  rw [utf8Bytes_cons, enc_slash]
  simp only [List.singleton_append, List.length_cons, Nat.lt_add_left_iff_pos, eq_iff_iff]
  constructor
  · intro h; cases rest with
    | nil => simp [utf8Bytes] at h
    | cons _ _ => simp
  · intro h; cases rest with
    | nil => simp at h
    | cons c cs => rw [utf8Bytes_cons]; simp [List.length_append]; exact Or.inl c.utf8Size_pos

theorem pathValidB_utf8 (cs : List Char) : pathValidB (utf8Bytes cs) = pathValid cs := by
  unfold pathValidB pathValid
  cases cs with
  | nil => rfl
  | cons c rest =>
    by_cases hc : c = '/'
    · subst hc
      rw [doubleSlashB_utf8, getLast_utf8 (List.cons_ne_nil _ _)]
      have := length_utf8_gt (rest := rest)
      rw [utf8Bytes_cons, enc_slash] at this ⊢
      simp only [List.singleton_append, List.head?_cons, beq_self_eq_true, Bool.true_and] at this ⊢
      simp only [this]
    · obtain ⟨e, es, he, hne⟩ := head_enc_ne hc
      rw [utf8Bytes_cons, he]
      simp only [List.cons_append, List.head?_cons, Option.some_beq_some, beq_false_of_ne hne,
        beq_false_of_ne hc, Bool.false_and]

/-- The components of bytes, split at each `/`, as `splitSlash` splits
characters. -/
def splitB : List UInt8 → List (List UInt8)
  | [] => [[]]
  | x :: rest =>
    if x = 47 then [] :: splitB rest
    else match splitB rest with
      | [] => [[x]]
      | w :: ws => (x :: w) :: ws

theorem splitB_ne_nil (R : List UInt8) : splitB R ≠ [] := by
  cases R with
  | nil => simp [splitB]
  | cons x rest =>
    rw [splitB]
    split
    · simp
    · split <;> simp

theorem splitB_append_of {X : List UInt8} (hX : (47 : UInt8) ∉ X) (Y : List UInt8) :
    splitB (X ++ Y) = match splitB Y with
      | [] => [X]
      | w :: ws => (X ++ w) :: ws := by
  induction X with
  | nil =>
    rw [List.nil_append]
    cases h : splitB Y with
    | nil => exact absurd h (splitB_ne_nil Y)
    | cons w ws => simp
  | cons x X ih =>
    simp only [List.mem_cons, not_or] at hX
    rw [List.cons_append, splitB]
    simp only [Ne.symm hX.1, ↓reduceIte, ih hX.2]
    cases splitB Y <;> rfl

theorem splitB_utf8 : ∀ cs : List Char, splitB (utf8Bytes cs) = (splitSlash cs).map utf8Bytes
  | [] => rfl
  | c :: cs => by
    by_cases hc : c = '/'
    · subst hc
      rw [utf8Bytes_cons, enc_slash, List.singleton_append, splitB]
      simp only [↓reduceIte, splitB_utf8 cs]
      rfl
    · rw [utf8Bytes_cons, splitB_append_of (fun h => hc (mem_enc_slash h)), splitB_utf8 cs,
        splitSlash_cons hc]
      cases splitSlash cs with
      | nil => simp [utf8Bytes_cons, utf8Bytes_nil]
      | cons w ws => simp [utf8Bytes_cons]

/-- The components of bytes from the first `/` at `k` or their end on: the
bytes before it, then the components after it. -/
theorem splitB_at {R : List UInt8} {k : Nat} (hk : k ≤ R.length)
    (hne : ∀ j < k, R[j]! ≠ 47) (hend : k = R.length ∨ R[k]! = 47) :
    splitB R = R.take k :: (if k = R.length then [] else splitB (R.drop (k + 1))) := by
  have hX : (47 : UInt8) ∉ R.take k := by
    intro h
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem h
    simp only [List.length_take] at hj
    rw [List.getElem_take] at hjv
    exact hne j (by omega) (by rw [getElem!_pos R j (by omega), hjv])
  rcases hend with rfl | hend
  · rw [List.take_length]
    simp only [↓reduceIte]
    have := splitB_append_of (List.take_length ▸ hX) []
    rw [List.append_nil] at this
    rw [this]; simp [splitB]
  · have hlt : k < R.length := by
      rcases Nat.lt_or_ge k R.length with h | h
      · exact h
      · rw [getElem!_neg R k (by omega)] at hend; cases hend
    simp only [show k ≠ R.length by omega, ↓reduceIte]
    have h47 : R[k] = 47 := by rw [← getElem!_pos R k hlt]; exact hend
    conv => lhs; rw [← List.take_append_drop k R, List.drop_eq_getElem_cons hlt]
    rw [splitB_append_of hX, splitB]
    simp [h47]

/-! ## The lookup of a path on bytes -/

/-- The child of a node with a name, as `child_named` looks for it among the
nodes `ns` in their order, `found` the match before them: the one node that
matches, none, or `AmbiguousMapping` at a second match. -/
def scanChild (pred : Node → Bool) : List Node → Option Node → Except Error (Option Node)
  | [], found => .ok found
  | n :: ns, found =>
    if pred n then
      match found with
      | some _ => .error .ambiguousMapping
      | none => scanChild pred ns (some n)
    else scanChild pred ns found

theorem scanChild_some (pred : Node → Bool) (m : Node) : ∀ ns : List Node,
    scanChild pred ns (some m) = match ns.filter pred with
      | [] => .ok (some m)
      | _ :: _ => .error .ambiguousMapping
  | [] => rfl
  | n :: ns => by
    rw [scanChild, List.filter_cons]
    by_cases h : pred n
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact scanChild_some pred m ns

theorem scanChild_none (pred : Node → Bool) : ∀ ns : List Node,
    scanChild pred ns none = match ns.filter pred with
      | [] => .ok none
      | [n] => .ok (some n)
      | _ :: _ :: _ => .error .ambiguousMapping
  | [] => rfl
  | n :: ns => by
    rw [scanChild, List.filter_cons]
    by_cases h : pred n
    · simp only [h, ↓reduceIte, scanChild_some]
      cases ns.filter pred <;> rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact scanChild_none pred ns

/-- Whether a node is a child of `p` whose name has the bytes `c`. -/
def childPred (p : Node) (c : List UInt8) (n : Node) : Bool :=
  n.isChildOf p && n.name.toUTF8.toList == c

/-- `Fdt.descend` on components as bytes, each child looked for as
`child_named` does. -/
def descendB (T : Fdt) : List (List UInt8) → Option Node → Except Error (Option Node)
  | [], cur => .ok cur
  | _ :: _, none => .ok none
  | c :: rest, some p =>
    match scanChild (childPred p c) T.nodes none with
    | .ok r => descendB T rest r
    | .error e => .error e

theorem childPred_utf8 (p : Node) (c : List Char) :
    childPred p (utf8Bytes c) = fun n => n.isChildOf p && n.name.toList == c := by
  funext n
  simp only [childPred, toUTF8_toList]
  congr 1
  by_cases h : n.name.toList = c
  · simp [h]
  · simp only [beq_false_of_ne h]
    exact beq_false_of_ne fun e => h (utf8Bytes_inj e)

theorem descendB_utf8 (T : Fdt) : ∀ (cs : List (List Char)) (cur : Option Node),
    descendB T (cs.map utf8Bytes) cur = T.descend cs cur
  | [], _ => by simp [descendB, Fdt.descend]
  | _ :: _, none => by simp [descendB, Fdt.descend]
  | c :: rest, some p => by
    simp only [List.map_cons, descendB, childPred_utf8, scanChild_none, Fdt.descend]
    cases List.filter (fun n => n.isChildOf p && n.name.toList == c) T.nodes with
    | nil => exact descendB_utf8 T rest none
    | cons n ns =>
      cases ns with
      | nil => exact descendB_utf8 T rest (some n)
      | cons m ms => rfl

/-- `Fdt.findNode` on the bytes of the path. -/
theorem findNode_eq (T : Fdt) (p : String) : T.findNode p =
    if !pathValidB (utf8Bytes p.toList) then .error .badPath
    else if (utf8Bytes p.toList).length = 1 then .ok T.root
    else descendB T (splitB ((utf8Bytes p.toList).drop 1)) T.root := by
  unfold Fdt.findNode
  rw [pathValidB_utf8]
  dsimp only
  split
  · rfl
  · rename_i hv
    have hv' : pathValid p.toList = true := by simpa using hv
    have hh : p.toList.head? = some '/' := by
      simp only [pathValid, Bool.and_eq_true, beq_iff_eq] at hv'; exact hv'.1.1
    obtain ⟨rest, hr⟩ : ∃ rest, p.toList = '/' :: rest := by
      cases h : p.toList with
      | nil => rw [h] at hh; cases hh
      | cons c rest => rw [h] at hh; cases hh; exact ⟨rest, rfl⟩
    rw [hr, utf8Bytes_cons, enc_slash, List.singleton_append, List.drop_one, List.tail_cons,
      List.tail_cons, splitB_utf8, descendB_utf8]
    by_cases h0 : rest = []
    · subst h0; simp [utf8Bytes_nil]
    · have h1 : ¬ (47 :: utf8Bytes rest).length = 1 := by
        simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff]
        exact fun h => h0 (utf8Bytes_eq_nil.1 h)
      have h2 : ¬ (('/' :: rest) == ['/']) = true := by simp [h0]
      simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]

/-- Begin-node tokens with increasing offsets have distinct offsets. -/
theorem offset_inj {L : List Begin} (hs : L.Pairwise (fun a b => a.offset < b.offset))
    {i j : Nat} (hi : i < L.length) (hj : j < L.length) (h : L[i].offset = L[j].offset) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := List.pairwise_iff_getElem.1 hs i j hi hj hij; omega
  · rfl
  · have := List.pairwise_iff_getElem.1 hs j i hj hi hij; omega

/-- The token of a record has the offset of the token of `p` as its parent
exactly when `p` is the parent of the record. -/
theorem parent_offset_iff {recs : Array NodeRecord} {L : List Begin} (hb : BeginsOf recs L)
    (hs : L.Pairwise (fun a b => a.offset < b.offset)) {k p : Nat} (hk : k < L.length)
    (hp : p < L.length) :
    L[k].parent = some L[p].offset ↔ (recs[k]'(hb.1 ▸ hk)).parent = some p := by
  rw [(hb.2 k hk (hb.1 ▸ hk)).2]
  cases (recs[k]'(hb.1 ▸ hk)).parent with
  | none => simp
  | some q =>
    simp only [Option.bind_some, Option.some.injEq]
    constructor
    · intro h
      rcases Nat.lt_or_ge q L.length with hq | hq
      · rw [List.getElem?_eq_getElem hq, Option.map_some, Option.some.injEq] at h
        exact offset_inj hs hq hp h
      · rw [List.getElem?_eq_none hq] at h; cases h
    · rintro rfl; rw [List.getElem?_eq_getElem hp]; rfl

end Krepi.Proofs.Fdt.Refinement

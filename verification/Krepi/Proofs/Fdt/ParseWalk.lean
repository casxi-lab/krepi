module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas
public import Krepi.Proofs.Fdt.SpanLemmas

/-!
# Device tree: the invariants of the walk of the parse

The invariants that the parse keeps while it reads the reservation map and
walks the tokens of the structure block, from which every tree that it
accepts is well-formed:

- the depth of a node on the records alone (`recDepth`), equal to
  `Fdt.depth` (`depthFrom_eq_recDepth`), unchanged by a pushed record and by a
  change of properties, and independent of the fuel once parents precede
  their children;
- `RecordOk`, the rules of `Fdt.NodeWellFormed` with that depth; `OpenOk`, the
  open nodes as a chain of ancestors whose records hold the names of their
  frames; and `WalkOk`, both for a walk;
- `place_ok` and `walkTokens_ok`: each token that `decodeToken` gives keeps
  `WalkOk`, and a walk that succeeds gives 1 to `MAX_TOKENS` records each of
  which is `RecordOk`;
- `reservationsFrom_ok`: the entries of a reservation map that succeeds are at
  most `MAX_RESERVATIONS`, nonempty and pairwise apart.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Depth -/

/-- The depth of a node read on records alone, as `Fdt.depthFrom` reads it. -/
def recDepth (recs : Array NodeRecord) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    match (recs[i]?).bind (·.parent) with
    | some p => recDepth recs f p + 1
    | none => 0

/-- `Fdt.depthFrom` reads only the records of the tree. -/
theorem depthFrom_eq_recDepth (t : Fdt) : ∀ f i, t.depthFrom f i = recDepth t.records f i
  | 0, _ => rfl
  | f + 1, i => by
    rw [Fdt.depthFrom, recDepth]
    cases (t.records[i]?).bind (·.parent) with
    | none => rfl
    | some p => dsimp only; rw [depthFrom_eq_recDepth t f p]

/-- Every parent of a record precedes it. -/
def ParentsBelow (recs : Array NodeRecord) : Prop :=
  ∀ (j p : Nat), (recs[j]?).bind (fun r : NodeRecord => r.parent) = some p → p < j

/-- Records with the same parents have the same depths. -/
theorem recDepth_congr {recs recs' : Array NodeRecord}
    (h : ∀ j : Nat, (recs[j]?).bind (fun r : NodeRecord => r.parent) =
      (recs'[j]?).bind (fun r : NodeRecord => r.parent)) :
    ∀ f i, recDepth recs f i = recDepth recs' f i
  | 0, _ => rfl
  | f + 1, i => by
    rw [recDepth, recDepth, h i]
    cases (recs'[i]?).bind (·.parent) with
    | none => rfl
    | some p => dsimp only; rw [recDepth_congr h f p]

/-- A pushed record keeps the depths of the records before it. -/
theorem recDepth_push {recs : Array NodeRecord} (x : NodeRecord) (hp : ParentsBelow recs) :
    ∀ f i, i < recs.size → recDepth (recs.push x) f i = recDepth recs f i
  | 0, _, _ => rfl
  | f + 1, i, hi => by
    have hget : (recs.push x)[i]? = recs[i]? := by
      rw [Array.getElem?_push]; simp [Nat.ne_of_lt hi]
    rw [recDepth, recDepth, hget]
    cases hq : (recs[i]?).bind (·.parent) with
    | none => rfl
    | some p => dsimp only; rw [recDepth_push x hp f p (by have := hp i p hq; omega)]

/-- Once parents precede their children, enough fuel gives the depth. -/
theorem recDepth_fuel {recs : Array NodeRecord} (hp : ParentsBelow recs) :
    ∀ f g i, i < f → i < g → recDepth recs f i = recDepth recs g i
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, i, hf, hg => by
    rw [recDepth, recDepth]
    cases hq : (recs[i]?).bind (·.parent) with
    | none => rfl
    | some p =>
      have := hp i p hq
      dsimp only
      rw [recDepth_fuel hp f g p (by omega) (by omega)]

/-- A change that keeps parents keeps depths. -/
theorem recDepth_modify {recs : Array NodeRecord} (k : Nat) (g : NodeRecord → NodeRecord)
    (hg : ∀ r, (g r).parent = r.parent) (f i : Nat) :
    recDepth (recs.modify k g) f i = recDepth recs f i := by
  apply recDepth_congr
  intro j
  rw [Array.getElem?_modify]
  split
  · cases recs[j]? <;> simp [hg]
  · rfl

/-! ## Invariants -/

/-- The rules of a node as `Fdt.NodeWellFormed` states them, with the depth read on the records. -/
def RecordOk (recs : Array NodeRecord) (i : Nat) (r : NodeRecord) : Prop :=
  (if i = 0 then r.parent = none ∧ r.name = ""
   else (∃ p, r.parent = some p ∧ p < i) ∧ r.name ≠ "") ∧
  r.name.toList.all isNodeNameChar = true ∧
  recDepth recs (i + 1) i < MAX_DEPTH.toNat ∧
  r.properties.length ≤ MAX_PROPERTIES.toNat ∧
  (r.properties.map (·.1)).Pairwise (· ≠ ·) ∧
  ∀ q ∈ r.properties,
    q.1 ≠ "" ∧ q.1.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat ∧
      q.1.toList.all isPropertyNameChar = true

/-- The open nodes, innermost first, as the indices of their records and the names of their
properties: each has its record with properties of those names, a depth that is the number of open
nodes outside it and an index above theirs. -/
def OpenOk (recs : Array NodeRecord) : List (Nat × List String) → Prop
  | [] => True
  | (k, names) :: rest =>
    (∃ r, recs[k]? = some r ∧ r.properties.map (·.1) = names) ∧
    recDepth recs (k + 1) k = rest.length ∧ (∀ q ∈ rest, q.1 < k) ∧ OpenOk recs rest

/-- `OpenOk` on other records that agree on the open nodes. -/
theorem openOk_transfer {recs recs' : Array NodeRecord} :
    ∀ {s : List (Nat × List String)}, OpenOk recs s →
      (∀ q ∈ s, recs'[q.1]? = recs[q.1]? ∧
        recDepth recs' (q.1 + 1) q.1 = recDepth recs (q.1 + 1) q.1) →
      OpenOk recs' s
  | [], _, _ => trivial
  | (k, names) :: rest, ⟨⟨r, hr, hn⟩, hd, hlt, hs⟩, h => by
    obtain ⟨h1, h2⟩ := h (k, names) List.mem_cons_self
    refine ⟨⟨r, by rw [h1, hr], hn⟩, by rw [h2, hd], hlt, ?_⟩
    exact openOk_transfer hs fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The index and the property names of an open node. -/
def frameKey (f : Frame) : Nat × List String := (f.index, f.names)

/-- The invariant of a walk: every record keeps its rules, the open nodes are a chain of ancestors,
and the root has begun exactly when there is a record. -/
structure WalkOk (w : Walk) : Prop where
  nodes : ∀ i (h : i < w.records.size), RecordOk w.records i w.records[i]
  stack : OpenOk w.records (w.open_.map frameKey)
  seen : w.seenRoot = true ↔ 0 < w.records.size

/-- Records that keep their rules have their parents before them. -/
theorem parentsBelow_of {recs : Array NodeRecord}
    (h : ∀ i (hi : i < recs.size), RecordOk recs i recs[i]) : ParentsBelow recs := by
  intro j p hj
  obtain ⟨r, hr, hpar⟩ := Option.bind_eq_some_iff.1 hj
  obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.1 hr
  have := (h j hjs).1
  split at this
  · rw [this.1] at hpar; cases hpar
  · obtain ⟨⟨q, hq, hlt⟩, -⟩ := this
    rw [hq] at hpar; cases hpar; exact hlt

/-- What `decodeToken` checks of the token that it gives. -/
def TokenOk : Token → Prop
  | .beginNode name => name.toList.all isNodeNameChar = true
  | .property name _ =>
    name ≠ "" ∧ name.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat ∧
      name.toList.all isPropertyNameChar = true
  | _ => True

/-- A decoded token keeps `TokenOk`. -/
theorem decodeToken_ok {str strs : ByteArray} {c : Nat} {tok : Token} {next : Nat}
    (h : decodeToken str strs c = .ok (tok, next)) : TokenOk tok := by
  unfold decodeToken at h
  obtain ⟨tag, -, h⟩ := except_bind_ok.1 h
  split at h
  · obtain ⟨⟨name, e⟩, -, h⟩ := except_bind_ok.1 h
    obtain ⟨a, -, h⟩ := except_bind_ok.1 h
    obtain ⟨h1, h⟩ := except_jp_ok h
    have h := except_pure_ok.1 h
    cases h
    simpa [TokenOk] using h1
  · cases except_pure_ok.1 h; trivial
  · obtain ⟨a, -, h⟩ := except_bind_ok.1 h
    obtain ⟨b, -, h⟩ := except_bind_ok.1 h
    obtain ⟨e, -, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨⟨name, e'⟩, -, h⟩ := except_bind_ok.1 h
    obtain ⟨h1, h⟩ := except_jp_ok h
    obtain ⟨a, -, h⟩ := except_bind_ok.1 h
    cases except_pure_ok.1 h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at h1
    obtain ⟨⟨h1, h2⟩, h3⟩ := h1
    refine ⟨?_, Nat.le_of_not_lt h2, by simpa using h3⟩
    intro he; subst he; exact h1 rfl
  · cases except_pure_ok.1 h; trivial
  · cases except_pure_ok.1 h; trivial
  · exact absurd h (except_throw_ne _ _)

/-- `RecordOk` on other records with the same depth. -/
theorem recordOk_recDepth {recs recs' : Array NodeRecord} {i : Nat} {r : NodeRecord}
    (hd : recDepth recs' (i + 1) i = recDepth recs (i + 1) i)
      (h : RecordOk recs i r) : RecordOk recs' i r := by
  unfold RecordOk at h ⊢
  rw [hd]
  exact h

/-- Pushing a record that keeps its rules keeps the rules of every record. -/
theorem nodes_push {recs : Array NodeRecord}
    (hn : ∀ i (h : i < recs.size), RecordOk recs i recs[i])
    (x : NodeRecord) (hx : RecordOk (recs.push x) recs.size x) :
    ∀ i (h : i < (recs.push x).size), RecordOk (recs.push x) i (recs.push x)[i] := by
  intro i h
  rw [Array.getElem_push]
  split
  · rename_i hi
    exact recordOk_recDepth (recDepth_push x (parentsBelow_of hn) _ _ hi) (hn i hi)
  · have : i = recs.size := by simp at h; omega
    subst this; exact hx

/-- Changing a record into one that keeps its rules, its parent kept, keeps the rules of every
record. -/
theorem nodes_modify {recs : Array NodeRecord}
    (hn : ∀ i (h : i < recs.size), RecordOk recs i recs[i])
    (k : Nat) (g : NodeRecord → NodeRecord) (hg : ∀ r, (g r).parent = r.parent)
    (hk : ∀ hk : k < recs.size, RecordOk (recs.modify k g) k (g recs[k])) :
    ∀ i (h : i < (recs.modify k g).size), RecordOk (recs.modify k g) i (recs.modify k g)[i] := by
  intro i h
  have hi : i < recs.size := by simpa using h
  rw [Array.getElem_modify]
  split
  · rename_i hki
    subst hki
    exact hk hi
  · exact recordOk_recDepth (recDepth_modify k g hg _ _) (hn i hi)

/-! ## Places -/

/-- A begin node keeps `WalkOk` and adds one record. -/
theorem place_begin {w w' : Walk} {name : String} (hw : WalkOk w)
    (hc : name.toList.all isNodeNameChar = true) (h : w.place (.beginNode name) = .ok w') :
    WalkOk w' ∧ w'.records.size ≤ w.records.size + 1 := by
  obtain ⟨op, sr, recs⟩ := w
  obtain ⟨hn, hs, hseen⟩ := hw
  dsimp only at hn hs hseen
  have hpb := parentsBelow_of hn
  cases op with
  | nil =>
    rw [Walk.place] at h
    obtain ⟨h1, h⟩ := except_jp_ok h
    obtain ⟨-, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, ne_eq,
      Decidable.not_not] at h1
    obtain ⟨h1, rfl⟩ := h1
    have h0 : recs.size = 0 := by
      have := (not_congr hseen).1 (by simp [h1]); omega
    obtain rfl : recs = #[] := Array.size_eq_zero_iff.1 h0
    refine ⟨⟨?_, ?_, by simp⟩, by simp⟩
    · apply nodes_push hn
      simp [RecordOk, recDepth, MAX_DEPTH]
    · simp [frameKey, OpenOk, recDepth]
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨h1, h⟩ := except_jp_ok h
    obtain ⟨h2, h⟩ := except_jp_ok h
    replace h := except_pure_ok.1 h
    subst h
    simp only [List.map, frameKey, OpenOk] at hs
    obtain ⟨⟨r, hr, hrn⟩, hd, hlt, hs⟩ := hs
    have hfi : f.index < recs.size := (Array.getElem?_eq_some_iff.1 hr).1
    have hdepth : recDepth (recs.push ⟨name, some f.index, []⟩) (recs.size + 1) recs.size =
        rest.length + 1 := by
      rw [recDepth]
      simp only [Array.getElem?_push_size, Option.bind_some]
      rw [recDepth_push _ hpb _ _ hfi, recDepth_fuel hpb _ (f.index + 1) _ hfi (by omega), hd]
      simp
    refine ⟨⟨?_, ?_, by simp⟩, by simp⟩
    · apply nodes_push hn
      simp only [RecordOk, Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hfi), ite_false]
      refine ⟨⟨⟨f.index, rfl, hfi⟩, h1⟩, hc, ?_, by simp, by simp, by simp⟩
      simp only [List.length_cons, Nat.not_le] at h2
      calc _ = rest.length + 1 := hdepth
        _ < _ := h2
    · simp only [List.map, frameKey, OpenOk]
      refine ⟨⟨⟨name, some f.index, []⟩, by simp, rfl⟩, hdepth.trans (by simp), ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons, List.mem_map] at hq
        rcases hq with rfl | ⟨g, hg, rfl⟩
        · exact hfi
        · exact Nat.lt_trans (hlt _ (List.mem_map.2 ⟨g, hg, rfl⟩)) hfi
      · refine ⟨⟨r, ?_, hrn⟩, ?_, hlt, ?_⟩
        · rw [Array.getElem?_push]; simp [Nat.ne_of_lt hfi, hr]
        · rw [recDepth_push _ hpb _ _ hfi, hd]
        · refine openOk_transfer hs fun q hq => ?_
          have hq' : q.1 < recs.size := Nat.lt_trans (hlt q hq) hfi
          refine ⟨?_, recDepth_push _ hpb _ _ hq'⟩
          rw [Array.getElem?_push]; simp [Nat.ne_of_lt hq']

/-- A property keeps `WalkOk` and adds no record. -/
theorem place_property {w w' : Walk} {name : String} {value : ByteArray} (hw : WalkOk w)
    (hc : name ≠ "" ∧ name.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat ∧
      name.toList.all isPropertyNameChar = true)
    (h : w.place (.property name value) = .ok w') :
    WalkOk w' ∧ w'.records.size ≤ w.records.size + 1 := by
  obtain ⟨op, sr, recs⟩ := w
  obtain ⟨hn, hs, hseen⟩ := hw
  dsimp only at hn hs hseen
  cases op with
  | nil => rw [Walk.place] at h; exact absurd h (except_throw_ne _ _)
  | cons f rest =>
    rw [Walk.place] at h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨h2, h⟩ := except_jp_ok h
    obtain ⟨h3, h⟩ := except_jp_ok h
    have h := except_pure_ok.1 h
    subst h
    simp only [List.map, frameKey, OpenOk] at hs
    obtain ⟨⟨r, hr, hrn⟩, hd, hlt, hs⟩ := hs
    have hfi : f.index < recs.size := (Array.getElem?_eq_some_iff.1 hr).1
    have hrf : recs[f.index] = r := (Array.getElem?_eq_some_iff.1 hr).2
    have hg : ∀ r : NodeRecord,
        ({ r with properties := r.properties ++ [(name, value)] } : NodeRecord).parent = r.parent :=
      fun _ => rfl
    simp only [Nat.not_lt] at h2
    simp only [List.contains_iff_mem] at h3
    refine ⟨⟨?_, ?_, by simpa using hseen⟩, by simp⟩
    · apply nodes_modify hn f.index _ hg
      intro hk
      have := hn f.index hk
      rw [hrf] at this ⊢
      obtain ⟨ha, hb, hc', -, he, hf⟩ := this
      refine ⟨ha, hb, by rw [recDepth_modify _ _ hg]; exact hc', ?_, ?_, ?_⟩
      · have := congrArg List.length hrn
        simp only [List.length_map] at this
        simp only [List.length_append, List.length_singleton, this]
        exact h2
      · simp only [List.map_append, List.map_cons, List.map_nil, hrn]
        rw [List.pairwise_append]
        refine ⟨hrn ▸ he, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb heq
        simp only [List.mem_singleton] at hb
        subst hb heq
        simp_all
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hf q hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact hc
    · simp only [List.map, frameKey, OpenOk]
      refine ⟨⟨{ r with properties := r.properties ++ [(name, value)] },
        by simp [Array.getElem?_modify, hr], by simp [hrn]⟩,
        by rw [recDepth_modify _ _ hg, hd], hlt, ?_⟩
      refine openOk_transfer hs fun q hq => ⟨?_, recDepth_modify _ _ hg _ _⟩
      have := Nat.ne_of_gt (hlt q hq)
      simp [Array.getElem?_modify, this]

/-- Every token that `decodeToken` gives keeps `WalkOk` and adds at most one record. -/
theorem place_ok {w w' : Walk} {tok : Token} (hw : WalkOk w) (ht : TokenOk tok)
    (h : w.place tok = .ok w') : WalkOk w' ∧ w'.records.size ≤ w.records.size + 1 := by
  cases tok with
  | beginNode name => exact place_begin hw ht h
  | property name value => exact place_property hw ht h
  | endNode =>
    obtain ⟨op, sr, recs⟩ := w
    obtain ⟨hn, hs, hseen⟩ := hw
    cases op with
    | nil => cases h
    | cons f rest =>
      cases h
      exact ⟨⟨hn, hs.2.2.2, hseen⟩, by simp⟩
  | nop => cases h; exact ⟨hw, by omega⟩
  | endStructure => cases h; exact ⟨hw, by omega⟩

/-- The walk before the first token keeps `WalkOk`. -/
theorem walkOk_start : WalkOk Walk.start :=
  ⟨fun _ h => absurd h (by simp [Walk.start]), trivial, by simp [Walk.start]⟩

/-- A walk that succeeds gives 1 to `MAX_TOKENS` records, each of which keeps its rules. -/
theorem walkTokens_ok {str strs : ByteArray} :
    ∀ (fuel c : Nat) (w : Walk) (recs : Array NodeRecord), WalkOk w →
      w.records.size + fuel ≤ MAX_TOKENS.toNat → walkTokens str strs fuel c w = .ok recs →
      (∀ i (h : i < recs.size), RecordOk recs i recs[i]) ∧ 0 < recs.size ∧
        recs.size ≤ MAX_TOKENS.toNat
  | 0, _, _, _, _, _, h => by rw [walkTokens] at h; cases h
  | fuel + 1, c, w, recs, hw, hf, h => by
    rw [walkTokens] at h
    obtain ⟨⟨tok, next⟩, hd, h⟩ := except_bind_ok.1 h
    have ht := decodeToken_ok hd
    cases tok with
    | endStructure =>
      obtain ⟨h1, h⟩ := except_jp_ok h
      cases except_pure_ok.1 h
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at h1
      exact ⟨hw.nodes, hw.seen.1 h1.1.1, by omega⟩
    | beginNode name =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hw', hs'⟩ := place_ok hw ht hp
      exact walkTokens_ok fuel next w' recs hw' (by omega) h
    | property name value =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hw', hs'⟩ := place_ok hw ht hp
      exact walkTokens_ok fuel next w' recs hw' (by omega) h
    | endNode =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hw', hs'⟩ := place_ok hw ht hp
      exact walkTokens_ok fuel next w' recs hw' (by omega) h
    | nop =>
      obtain ⟨w', hp, h⟩ := except_bind_ok.1 h
      obtain ⟨hw', hs'⟩ := place_ok hw ht hp
      exact walkTokens_ok fuel next w' recs hw' (by omega) h

/-! ## The reservation map -/

/-- The rules of the reservation entries that `reservationsFrom` keeps. -/
def ReservationsOk (l : List Span) : Prop :=
  l.length ≤ MAX_RESERVATIONS.toNat ∧ (∀ s ∈ l, s.Nonempty) ∧
    l.Pairwise (fun a b => a.overlaps b = false)

/-- A reservation map that succeeds keeps the rules of its entries. -/
theorem reservationsFrom_ok (h : Header) :
    ∀ (fuel c : Nat) (earlier rs : List Span), ReservationsOk earlier →
      reservationsFrom h fuel c earlier = .ok rs → ReservationsOk rs
  | 0, _, _, _, _, hr => by rw [reservationsFrom] at hr; cases hr
  | fuel + 1, c, earlier, rs, he, hr => by
    rw [reservationsFrom] at hr
    obtain ⟨e, -, hr⟩ := except_bind_ok.1 hr
    obtain ⟨-, hr⟩ := except_jp_ok hr
    obtain ⟨-, hr⟩ := except_jp_ok hr
    obtain ⟨start, -, hr⟩ := except_bind_ok.1 hr
    obtain ⟨size, -, hr⟩ := except_bind_ok.1 hr
    split at hr
    · cases except_pure_ok.1 hr; exact he
    · obtain ⟨h1, hr⟩ := except_jp_ok hr
      obtain ⟨span, hspan, hr⟩ := except_bind_ok.1 hr
      obtain ⟨h2, hr⟩ := except_jp_ok hr
      obtain ⟨h3, hr⟩ := except_jp_ok hr
      obtain ⟨hv, rfl⟩ := span_new_ok.1 hspan
      obtain ⟨hl, hne, hp⟩ := he
      refine reservationsFrom_ok h fuel e _ rs ⟨?_, ?_, ?_⟩ hr
      · simp only [List.length_append, List.length_singleton]; omega
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact hne s hs
        · simp only [List.mem_singleton] at hs
          subst hs
          exact ⟨h2, hv⟩
      · rw [List.pairwise_append]
        refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at h3
        exact h3 a ha

end Krepi.Proofs.Fdt

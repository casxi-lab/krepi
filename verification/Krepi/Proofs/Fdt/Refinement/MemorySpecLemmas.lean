module

public import Krepi.Proofs.Fdt.Refinement.TreeSpecLemmas
public import Krepi.Proofs.Fdt.Refinement.NodePropertySpecLemmas
public import Krepi.Proofs.Fdt.Refinement.ParseWalkSpecLemmas
public import Krepi.Spec.Fdt.Discovery

/-!
# Device tree: lemmas about the specification of the memory discovery

Lemmas about `Krepi.Spec.Fdt.Discovery` and about the `?` operator of the
code on a function that returns its result with a state, for the refinement
proof of `Fdt::discover_memory`. The module imports no generated
definitions, so it is built once and not again for every mutant of the code.

- The `?` operator with a state: `try_state_spec` (a call whose result agrees
  with a step of the specification continues on a related value, and its
  failure agrees with the failure of the block that starts with that step,
  for a function that returns its result with the memory map it wrote) with
  `from_residual_state_spec`, the failure that the code returns with its
  state, and `agrees_bind_ok`, the agreement with the image of a step.
- Values and lists: `word64_eq_zero_iff` and `isPrefixOf_iff_take`; the
  update of an array at its count is `take_set_succ` of
  `Krepi.Proofs.Fdt.Refinement.ParseWalkSpecLemmas`.
- Names and paths: `isMemoryName_eq` (a memory name by its bytes),
  `findNode_slash_eq_root` (the lookup of `/` is the root) and
  `findNode_reserved_memory` (the lookup of `/reserved-memory` as
  `descendB` on its bytes).
- The steps of the discovery, each the definition in the form that the
  proofs of the code walk: `ramOfChild_eq`, `reservedOfChild_eq` with
  `reservedOfChild_snd` (a reserved child adds at most one dynamic
  reservation), `reservedMemoryBinding_eq`, `reservedMemory_eq`,
  `discoverMemory_none` and `discoverMemory_some` (the discovery by the root
  of the tree).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open Krepi.Statements Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The `?` operator with a state -/

/-- The `?` operator as one step of a proof of a function that returns its
result with a state: the code `branch r >>= C` of `f(..)?`, whose result `r`
agrees with the step `E` of the specification, agrees with the block `E >>= k`
when the continuation on a success agrees with `k` of the related value, and
`C` returns the failure on a failure (`from_residual_state_spec`). -/
theorem try_state_spec {α β σ δ ε ε' : Type} {rel : α → β → Prop} {R : σ → δ → Prop}
    {err : ε → ε'} {r : core.result.Result α ε} {E : Except ε' β} {k : β → Except ε' δ}
    {C : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α →
      Result (core.result.Result Unit ε × σ)}
    (hr : Agrees rel err r E)
    (he : ∀ e, C (.Break (.Err e)) ⦃ out _ => out = .Err e ⦄)
    (hk : ∀ a b, rel a b → E = .ok b →
      C (.Continue a) ⦃ out s => Agrees (fun _ d => R s d) err out (k b) ⦄) :
    (core.result.Result.Insts.CoreOpsTry.branch r >>= C) ⦃ out s =>
      Agrees (fun _ d => R s d) err out (E >>= k) ⦄ := by
  cases r with
  | Ok a =>
    obtain ⟨b, hE, hab⟩ := agrees_ok_iff.mp hr
    subst hE
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    exact hk a b hab rfl
  | Err e =>
    rw [agrees_err_iff] at hr; subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    refine spec_mono (he e) ?_
    rintro ⟨out, s⟩ h
    simp only [uncurry'_pair] at h ⊢
    subst h; rfl

/-- The failure branch of `?` in a function that returns its result with a
state: the failure, with the state. -/
theorem from_residual_state_spec {σ ε : Type} (e : ε) (s : σ) :
    (do
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
        (core.convert.FromSame ε) (.Err e)
      ok (r, s)) ⦃ out _ => out = .Err e ⦄ := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- A result that agrees with `E` agrees with the image of `E`, for a
relation that the image keeps. -/
theorem agrees_bind_ok {α β δ ε ε' : Type} {rel : α → β → Prop} {rel' : α → δ → Prop}
    {err : ε → ε'} {r : core.result.Result α ε} {E : Except ε' β} {g : β → δ}
    (h : Agrees rel err r E) (hg : ∀ a b, rel a b → rel' a (g b)) :
    Agrees rel' err r (E >>= fun b => .ok (g b)) := by
  cases r with
  | Ok a =>
    obtain ⟨b, rfl, hab⟩ := agrees_ok_iff.mp h
    exact hg a b hab
  | Err e =>
    rw [agrees_err_iff] at h
    rw [h]
    rfl

/-! ## Values and lists -/

/-- A word of the code is 0 exactly when its value is. -/
theorem word64_eq_zero_iff (x : U64) : word64 x = 0 ↔ x = 0#u64 := by
  rw [word64_eq_iff]
  exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => by rw [h]; rfl⟩

/-- A prefix of a list is its first items. -/
theorem isPrefixOf_iff_take {α : Type} [BEq α] [LawfulBEq α] {P W : List α} :
    P.isPrefixOf W = true ↔ W.take P.length = P := by
  rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, eq_comm]

/-! ## Names and paths -/

/-- A memory name by its bytes: `memory`, or bytes that start with those of
`memory@`. -/
theorem isMemoryName_eq (nm : String) :
    isMemoryName nm = (decide (nm = "memory") ||
      ([109, 101, 109, 111, 114, 121, 64] : List UInt8).isPrefixOf nm.toUTF8.toList) := by
  unfold isMemoryName
  have h1 : (nm == "memory") = decide (nm = "memory") := by
    by_cases h : nm = "memory" <;> simp [h]
  have h2 : "memory@".toByteArray.toList = [109, 101, 109, 111, 114, 121, 64] := by
    rw [← String.toUTF8_eq_toByteArray, toUTF8_toList]; rfl
  rw [String.toUTF8_eq_toByteArray, h1, h2]

/-- The lookup of `/` is the root. -/
theorem findNode_slash_eq_root (T : Fdt) : T.findNode "/" = .ok T.root := by
  rw [findNode_eq]; rfl

/-- The lookup of `/reserved-memory`, on the bytes of the path as
`find_path` walks them. -/
theorem findNode_reserved_memory (T : Fdt) :
    T.findNode "/reserved-memory" =
      descendB T (splitB ((utf8Bytes "/reserved-memory".toList).drop 1)) T.root := by
  rw [findNode_eq]; rfl

/-! ## The steps of the discovery -/

/-- `ramOfChild` with its checks in the order of the code. -/
theorem ramOfChild_eq (ram : List Span) (n : Node) :
    ramOfChild ram n = n.stringProperty "device_type" >>= fun dt =>
      if !(isMemoryName n.name || dt == some "memory") then .ok ram else
      n.enabled >>= fun en => if !en then .ok ram else
      if !(isMemoryName n.name && dt == some "memory") then .error .badProperty else
      n.reg >>= fun reg => reg.entries.foldlM addRam ram := by
  unfold ramOfChild
  rfl

/-- `reservedOfChild` with its checks in the order of the code. -/
theorem reservedOfChild_eq (acc : List ReservedRegion × Nat) (n : Node) :
    reservedOfChild acc n = n.enabled >>= fun en => if !en then .ok acc else
      n.flag "no-map" >>= fun noMap => n.flag "reusable" >>= fun reusable =>
      if noMap && reusable then .error .badProperty else
      match n.property "reg", n.property "size" with
      | none, none => .error .missingProperty
      | none, some _ => .ok (acc.1, acc.2 + 1)
      | some _, _ => n.reg >>= fun reg =>
        reg.entries.foldlM (addReservedSpan noMap reusable) acc.1 >>= fun reserved =>
        .ok (reserved, acc.2) := by
  unfold reservedOfChild
  rfl

/-- A reserved child adds at most one dynamic reservation. -/
theorem reservedOfChild_snd {acc acc' : List ReservedRegion × Nat} {n : Node}
    (h : reservedOfChild acc n = .ok acc') : acc'.2 ≤ acc.2 + 1 := by
  rw [reservedOfChild_eq] at h
  simp only [Bind.bind, Except.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp

/-- `reservedMemoryBinding` with its checks in the order of the code. -/
theorem reservedMemoryBinding_eq (parent root : Node) :
    reservedMemoryBinding parent root =
      if (parent.property "#address-cells").isNone || (parent.property "#size-cells").isNone then
        .error .badProperty
      else parent.addressCells >>= fun pa => root.addressCells >>= fun ra =>
        if pa ≠ ra then .error .badProperty
        else parent.sizeCells >>= fun ps => root.sizeCells >>= fun rs =>
          if ps ≠ rs then .error .badProperty
          else match parent.property "ranges" with
            | some value => if value.size ≠ 0 then .error .badProperty else .ok ()
            | none => .error .badProperty := by
  unfold reservedMemoryBinding
  rfl

/-- `Fdt.reservedMemory` with its steps in the order of the code. -/
theorem reservedMemory_eq (t : Fdt) (root : Node) (mapped : List ReservedRegion) :
    t.reservedMemory root mapped = t.findNode "/reserved-memory" >>= fun o =>
      match o with
      | none => .ok (mapped, 0)
      | some parent => reservedMemoryBinding parent root >>= fun _ =>
        parent.enabled >>= fun en => if !en then .ok (mapped, 0) else
        (t.nodes.filter (·.isChildOf parent)).foldlM reservedOfChild (mapped, 0) := by
  unfold Fdt.reservedMemory
  rfl

/-- `Fdt.discoverMemory` of a tree without a root. -/
theorem discoverMemory_none {t : Fdt} (h : t.root = none) :
    t.discoverMemory =
      t.reservations.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) [] >>= fun _ =>
        .error .badTree := by
  unfold Fdt.discoverMemory
  rw [findNode_slash_eq_root, h]
  rfl

/-- `Fdt.discoverMemory` of a tree with a root, with its steps in the order
of the code. -/
theorem discoverMemory_some {t : Fdt} {root : Node} (h : t.root = some root) :
    t.discoverMemory =
      t.reservations.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) [] >>= fun mapped =>
      (t.nodes.filter (·.isChildOf root)).foldlM ramOfChild [] >>= fun ram =>
      if ram.isEmpty then .error .noMemory else
      t.reservedMemory root mapped >>= fun p =>
      match p with
      | (reserved, dynamic) => .ok { ram, reserved, dynamic := UInt64.ofNat dynamic } := by
  unfold Fdt.discoverMemory
  rw [findNode_slash_eq_root, h]
  rfl

end Krepi.Proofs.Fdt.Refinement

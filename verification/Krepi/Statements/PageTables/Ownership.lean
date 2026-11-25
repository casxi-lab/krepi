module

public import Krepi.Statements.PageTables.Representation
public import Krepi.SpecProperties.PageTables.Invariants

/-!
# Page tables: refinement of the page ownership table

One statement for each function of lines 113 to 117 of the entry table of
the contract (`docs/domains/memory/page-tables/contract.md`): for every
input of its machine widths, under the premises that its arguments need,
the function returns, and its result agrees with that of its function of
`Krepi.Spec.PageTables` through the representation of
`Krepi.Statements.PageTables.Representation`, the same error with the same
priority included. A write entry returns its table, which stands for the
table that its specification gives; on a failure it returns the table
unchanged. The entries on a table take `Ownership.Invariant`, which
`Ownership::new` establishes and the write entries preserve, and `assign`
takes a choice that `choose` gave on the same table (`Ownership.Chose`),
premises of the proof path. The theorems below
`Krepi.Proofs.PageTables.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice U8 U64 Usize)
open KrepiGen.PageTables
open Krepi.Spec.PageTables

namespace Krepi.Statements.PageTables

/-- `Ownership::new(arena, banks, exclusions)`: a table that stands for that
of `Ownership.new` of the arena, the ranges and the exclusions, of the
capacities `E` and `X`, or its error.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipNew : Prop :=
  ∀ (E X : Usize) (arena : U64) (banks : Slice page_tables.PhysRange)
    (exclusions : Slice page_tables.Exclusion) (Bs : List PhysRange) (Xs : List Exclusion),
    ListRel PhysRangeRepr banks.val Bs → ListRel ExclusionRepr exclusions.val Xs →
    page_tables.ownership.Ownership.new E X arena banks exclusions ⦃ r =>
      Agrees OwnershipRepr ownershipErrorOf r
        (Ownership.new (E := E.val) (X := X.val) (word64 arena) Bs Xs) ⦄

/-- `Ownership::choose(owner, pages, alignment, placement)`: the choice of
`Ownership.choose`, or its error.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipChoose : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val)
    (owner pages alignment : U64) (placement : page_tables.Placement) (P : Placement),
    OwnershipRepr t T → T.Invariant → PlacementRepr placement P →
    page_tables.ownership.placement.Ownership.choose t owner pages alignment placement ⦃ r =>
      Agrees ChoiceRepr ownershipErrorOf r
        (T.choose (word64 owner) (word64 pages) (word64 alignment) P) ⦄

/-- `Ownership::assign(choice, zeroed)`: the table and the receipt of
`Ownership.assign` of a choice that `choose` gave on the table, or its error
with the table unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipAssign : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val)
    (choice : page_tables.Choice) (C : Choice) (zeroed : Bool),
    OwnershipRepr t T → T.Invariant → ChoiceRepr choice C → T.Chose C →
    page_tables.ownership.placement.Ownership.assign t choice zeroed ⦃ r t' =>
      Writes OwnershipRepr AllocationRepr (ownershipErrorOf · = ·) t r t' (T.assign C zeroed) ⦄

/-- `Ownership::reserve(owner, pages, alignment, placement)`: the table and
the reservation of `Ownership.reserve`, or its error with the table
unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipReserve : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val)
    (owner pages alignment : U64) (placement : page_tables.Placement) (P : Placement),
    OwnershipRepr t T → T.Invariant → PlacementRepr placement P →
    page_tables.ownership.placement.Ownership.reserve t owner pages alignment placement ⦃ r t' =>
      Writes OwnershipRepr ReservationRepr (ownershipErrorOf · = ·) t r t'
        (T.reserve (word64 owner) (word64 pages) (word64 alignment) P) ⦄

/-- `Reservation::initialized(zeroed)`: the packet of
`Reservation.initialized`, or the reservation that it retains.
Feature: `krepi.kernel.kernel-memory`. -/
def ReservationInitialized : Prop :=
  ∀ (r : page_tables.Reservation) (R : Reservation) (zeroed : Bool), ReservationRepr r R →
    page_tables.ownership.receipts.Reservation.initialized r zeroed ⦃ x =>
      match x, R.initialized zeroed with
      | .Ok packet, .packet X => InitializedRepr packet X
      | .Err kept, .retained K => ReservationRepr kept K
      | _, _ => False ⦄

/-- `Ownership::publish(owner, packet)`: the table and the receipt of
`Ownership.publish`, or its error and the packet with the table unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipPublish : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val) (owner : U64)
    (packet : page_tables.Initialized) (I : Initialized),
    OwnershipRepr t T → T.Invariant → InitializedRepr packet I →
    page_tables.ownership.receipts.Ownership.publish t owner packet ⦃ r t' =>
      Writes OwnershipRepr AllocationRepr
        (fun (e, x) (E, Y) => ownershipErrorOf e = E ∧ InitializedRepr x Y) t r t'
        (T.publish (word64 owner) I) ⦄

/-- `Ownership::cancel(owner, reservation)`: the table of `Ownership.cancel`,
or its error and the reservation with the table unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipCancel : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val) (owner : U64)
    (reservation : page_tables.Reservation) (R : Reservation),
    OwnershipRepr t T → T.Invariant → ReservationRepr reservation R →
    page_tables.ownership.receipts.Ownership.cancel t owner reservation ⦃ r t' =>
      Writes OwnershipRepr (fun _ _ => True)
        (fun (e, x) (E, Y) => ownershipErrorOf e = E ∧ ReservationRepr x Y) t r t'
        ((T.cancel (word64 owner) R).map (·, ())) ⦄

/-- `Ownership::release(owner, receipt)`: the table of `Ownership.release`,
or its error with the table unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipRelease : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val) (owner : U64)
    (receipt : page_tables.Allocation) (A : Allocation),
    OwnershipRepr t T → T.Invariant → AllocationRepr receipt A →
    page_tables.ownership.receipts.Ownership.release t owner receipt ⦃ r t' =>
      Writes OwnershipRepr (fun _ _ => True) (ownershipErrorOf · = ·) t r t'
        ((T.release (word64 owner) A).map (·, ())) ⦄

/-- `Ownership::owner(address)`: the owner of the page of the address,
`Ownership.owner`, none outside the managed pages.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipOwner : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val) (address : U64),
    OwnershipRepr t T → T.Invariant →
    page_tables.ownership.Ownership.owner t address ⦃ o =>
      o.map ownerOf = T.owner (word64 address) ⦄

/-- `Ownership::validate(owner, allocation, state)`: success exactly when
`Ownership.validate` succeeds, and its error otherwise.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipValidate : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val) (owner : U64)
    (allocation : page_tables.Allocation) (A : Allocation) (state : page_tables.HoldState),
    OwnershipRepr t T → T.Invariant → AllocationRepr allocation A →
    page_tables.ownership.receipts.Ownership.validate t owner allocation state ⦃ r =>
      Agrees (fun _ _ => True) ownershipErrorOf r
        (T.validate (word64 owner) A (holdStateOf state)) ⦄

/-- `Ownership::stats()`: the statistics of `Ownership.stats`.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipStats : Prop :=
  ∀ (E X : Usize) (t : page_tables.Ownership E X) (T : Ownership E.val X.val),
    OwnershipRepr t T → T.Invariant →
    page_tables.ownership.Ownership.stats t ⦃ s => StatsRepr s T.stats ⦄

end Krepi.Statements.PageTables

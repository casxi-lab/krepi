-- Reviewed external function of the qualification case `str_from`.
-- `cargo xtask formal run` installs this file in place of the template that
-- Aeneas generates. Only the reached From<&str> method is replaced: it is
-- the qualification definition `Krepi.Qualification.Models.FromStr.fromStr`,
-- which decodes the bytes of the slice as UTF-8. Bytes that are not UTF-8,
-- which no Rust &str holds, give the undefined-behaviour error. Allocation
-- failure is outside the definition.
module
public import Aeneas
public import KrepiGen.Qual.StrFrom.Types
public import Krepi.Qualification.Models.FromStr
@[expose] public section
open Aeneas Aeneas.Std Result
open KrepiGen.Qual.StrFrom

/-- The exact generated signature of From<&str> for String. -/
@[rust_fun
  "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from"]
def alloc.string.String.Insts.CoreConvertFromShared0Str.from
    : Str → Result String := Krepi.Qualification.Models.FromStr.fromStr

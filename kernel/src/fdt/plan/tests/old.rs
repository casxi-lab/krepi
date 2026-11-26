//! The boot memory map entry on a boot memory before it checked the number
//! of further spans right after the window: the code of krepi commit
//! 512ed1b at the lines below, copied verbatim with the suffix `_old` added
//! to the name of the function, for the differential tests, which compare
//! it with the code that replaced it. The functions that it calls did not
//! change; they are those of the module, and the copy reaches them through
//! `super::super`.
//!
//! - `kernel/src/fdt/plan.rs:287-308`: `MemoryPlan::from_boot_memory`.
//!
//! Feature: krepi.platform.device-tree

use super::super::*;

impl MemoryPlan {
    /// [`MemoryPlan::new`] with the RAM ranges of the boot memory `memory`,
    /// the boot storage of its image, its tree and then the further spans
    /// `more` of the board, such as the boot bundle, in this order, and its
    /// reserved regions as firmware reservations; more than two further
    /// spans make more than 4 spans of boot storage, `Capacity`.
    pub fn from_boot_memory_old(
        memory: &BootMemory,
        window: Span,
        more: &[Span],
    ) -> Result<MemoryPlan, PlanError> {
        check_window(window)?;
        let mut boot = [memory.image, memory.dtb, EMPTY, EMPTY];
        if more.len() <= 2 {
            let mut index = 0;
            while index < more.len() {
                boot[2 + index] = more[index];
                index += 1;
            }
        }
        let plan = build(memory.ram(), &boot, 2 + more.len(), memory.reserved())?;
        manage_window(plan, window)
    }
}

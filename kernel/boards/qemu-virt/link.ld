/* Feature: krepi.platform.qemu-virt-boot */
/* The layout of the QEMU virt images: the default image and the test images.
 * QEMU virt has at least 128 MiB of RAM at 0x4000_0000. The image starts
 * 2 MiB above it and leaves the first 2 MiB to the device tree that QEMU
 * places at the start of RAM: QEMU 11.1.2 builds a device tree of 1 MiB and
 * leaves it out when the image leaves too little room. The exception vectors
 * follow the cold entry, aligned to the 2 KiB that VBAR_EL1 requires. */
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x40200000, LENGTH = 0x07e00000 }
PHDRS {
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    data PT_LOAD FLAGS(6);
}
SECTIONS {
    . = ORIGIN(RAM);
    .text : ALIGN(4096) {
        __text_start = .;
        KEEP(*(.text.boot))
        KEEP(*(.text.vectors))
        *(.text .text.*)
        . = ALIGN(4096);
        __text_end = .;
    } > RAM :text
    .note.gnu.build-id : ALIGN(4096) {
        __rodata_start = .;
        __build_id_start = .;
        KEEP(*(.note.gnu.build-id))
        __build_id_end = .;
    } > RAM :rodata
    .rodata : ALIGN(4096) {
        *(.rodata .rodata.*)
        . = ALIGN(4096);
        __rodata_end = .;
    } > RAM :rodata
    .data : ALIGN(4096) {
        *(.data .data.*)
        *(.got .got.*)
    } > RAM :data
    .bss (NOLOAD) : ALIGN(4096) {
        __bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4096);
        __bss_end = .;
    } > RAM :data
    .stack (NOLOAD) : ALIGN(4096) {
        __stack_guard = .;
        . += 4096;
        __stack_bottom = .;
        . += 64K;
        __stack_top = .;
    } > RAM :data
    __image_end = .;
    /DISCARD/ : { *(.eh_frame .eh_frame_hdr) }
}
ASSERT(_start == ORIGIN(RAM), "entry must be the first instruction")
ASSERT((__exception_vectors & 0x7ff) == 0, "VBAR requires 2 KiB alignment")
ASSERT((__stack_bottom & 0xfff) == 0, "stack must be page aligned")
ASSERT((__stack_top & 0xfff) == 0, "stack end must be page aligned")
ASSERT(__image_end <= ORIGIN(RAM) + LENGTH(RAM), "image exceeds minimum guest RAM")

ASSERT(__build_id_end - __build_id_start == 36, "SHA-1 GNU build-id note must be 36 bytes")

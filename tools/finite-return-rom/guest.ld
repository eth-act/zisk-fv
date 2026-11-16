OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(5); }
SECTIONS
{
  . = 0x80000000;
  .text : { KEEP(*(.text.entry)) *(.text*) } :text
  /DISCARD/ : { *(.comment) *(.riscv.attributes) *(.eh_frame*) }
}

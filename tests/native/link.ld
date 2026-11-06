ENTRY(_start)
PHDRS {
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS {
  . = 0x10000;
  .text.protocol : { *(.text.protocol) } :text
  .text.start : { *(.text.start) } :text
  .rodata : { *(.rodata*) } :text
  . = 0x20000;
  .data : { *(.data*) } :data
  .bss : { *(.bss*) } :data
}

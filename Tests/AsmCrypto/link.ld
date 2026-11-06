ENTRY(_start)
PHDRS {
  text PT_LOAD FLAGS(5);
  state PT_LOAD FLAGS(6);
  input PT_LOAD FLAGS(4);
  constants PT_LOAD FLAGS(4);
  scratch PT_LOAD FLAGS(6);
  stack PT_LOAD FLAGS(6);
  output PT_LOAD FLAGS(6);
}
SECTIONS {
  . = 0x10000;
  .text.protocol : { *(.text.protocol) } :text
  . = 0x18000;
  .text.return : { *(.text.return) } :text
  .text.start : { *(.text.start) } :text
  . = 0x20000;
  .data.state : { *(.data.state) } :state
  . = 0x30000;
  .rodata.input : { *(.rodata.input) } :input
  . = 0x40000;
  .rodata.constants : { *(.rodata.constants) } :constants
  . = 0x50000;
  .data.scratch : { *(.data.scratch) } :scratch
  . = 0x60000;
  .data.stack : { *(.data.stack) } :stack
  . = 0x70000;
  .data.output : { *(.data.output) } :output
}

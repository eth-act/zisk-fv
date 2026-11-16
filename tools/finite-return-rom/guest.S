.option norvc
.option norelax
.section .text.entry,"ax",@progbits
.globl _start
.type _start,@function
_start:
    addi t0, zero, 1
    ret
.size _start, .-_start

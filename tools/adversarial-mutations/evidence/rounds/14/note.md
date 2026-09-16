`delta_addr === (addr - 'addr) * (1 - reset)` is the link between consecutive
MemAlign rows: it forces the address delta fed to the `MEMORY_ALIGN_ROM` lookup
to be the real difference between this row's address and the previous row's.
Deleting it frees `delta_addr` entirely, so a prover can present any address
progression to the ROM.

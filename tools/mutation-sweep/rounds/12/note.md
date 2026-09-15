`store_pc` selects "write the program counter to the destination", which is what
makes `JAL`/`JALR` save a return address. Deleting its booleanity lets a prover
choose any field element for it. The dropped constraint also renumbers every
later Main constraint, so this round doubles as a test of whether the model is
pinned to constraint *indices* as well as to constraint *content*.

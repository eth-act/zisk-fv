Not a test — but for a reason worth recording. The identity is inside
`if (stack_enabled) { … }`, and `main.pil:14` declares
`airtemplate Main(int N = 2**21, int RC = 2, int stack_enabled = 0, …)`, which
`zisk.pil` does not override. Ten `if (stack_enabled)` blocks in `main.pil` are
compile-time dead in the pinned configuration, so nothing downstream — pilout,
extraction or proof — can be sensitive to them.

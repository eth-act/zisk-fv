This is a commutativity control, not a defect injection: `fab * a[1] * b[3]`
became `fab * b[3] * a[1]`, which is the same polynomial. The pilout expression
tree changes and so does the emitted Lean text, so the round still exercises the
whole pipeline — but the circuit is unchanged and `lake build` must pass.

import Clean.Circuit.Channel

/-!
# Clean integration sanity check

Imports the smallest possible identifier from Clean to verify that
the `[[require]] name = "Clean" path = "build/clean-lean"` link in
`lakefile.toml` resolves and Clean's lib compiles transitively.

Deleted at Phase 6 cutover.
-/

example : True := trivial

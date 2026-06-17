# Starting point established + mission set

Mission set: build an accurate mental model of `zisk-fv`'s architecture in
order to re-architect it (proof structure first, then build system + CI). See
[[MISSION.md]].

**Prior knowledge (high):** expert in Lean 4, formal verification, and the
RISC-V / zkVM domain; is the primary author of the repo, built in a lightly-
supervised way with AI. Do not re-teach these.

**Prior knowledge (low):** self-rated "just the gist" of the repo's own
top-level pipeline — knows the pieces (flake / extraction / proof tower /
trust gate) exist but cannot confidently draw the data/proof flow between
them. This sets the zone of proximal development for early sessions: top-down
structural mapping, not Lean mechanics.

**Implication:** lessons teach *this repo's structure and seams*, pitched at a
domain expert. Lesson 0001 is the top-down territory map; subsequent lessons
drill into the proof tower (priority 1), the RHS circuit stack, the trust gate,
and the build/CI — each with an explicit re-architecture lens.

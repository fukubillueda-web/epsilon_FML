import LanglandsFirstMainLemma.Cases.WildEndpoints.Zero
import LanglandsFirstMainLemma.Cases.WildEndpoints.One.Final

/-!
# The endpoint conductors in wild prime degree

This file treats the two multiplicative conductors at which there is no
Lamprecht stationary layer.  The conductor-zero proof is carried out directly
with uniformizer denominators and the complete norm-character group.  For
conductor one we isolate the residue/trace comparison and the endpoint
discriminant calculation, and then assemble the complete product, retaining
the trivial-character term.

The stationary classes used below belong only to the nontrivial norm
characters, whose conductor is `t + 1 > 1`.  No stationary class is attached
to a character of conductor zero or one.

Source: Subsection `sec:wild-endpoints` and Lemma
`lem:endpoint-discriminant-congruence` of the authoritative manuscript.
-/

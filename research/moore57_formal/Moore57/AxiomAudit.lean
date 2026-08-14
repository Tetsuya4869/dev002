import Moore57.SRGConsequences
import Moore57.SRGRestricted
import Moore57.FixedPoints

/-!
# Axiom audit

This file is executed explicitly by CI.  Its output is checked for `sorryAx` so that
a future accidental `sorry` cannot silently preserve a green build for the central
formal results.
-/

#print axioms Moore57.no_commonGroupCase_of_fixedPointCount_56
#print axioms Moore57.SimpleGraph.IsSRGWith.gives_order56_latinCube
#print axioms Moore57.SimpleGraph.IsSRGWith.routeEndpoint_bijective
#print axioms Moore57.ShortCycleSystem.no_fullAllInvolution_of_no_restriction
#print axioms Moore57.SimpleGraph.IsSRGWith.no_allInvolution_of_no_restricted

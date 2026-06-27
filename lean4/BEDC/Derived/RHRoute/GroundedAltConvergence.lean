import BEDC.Derived.RHRoute.AltConvergence
import BEDC.Derived.LocatedReal.GroundedToleranceKit

/-!
The alternating series test, grounded in BEDC's concrete dyadic-tolerance
real-number metric (`groundedRatToleranceLaws`). Instantiating the generic
located-real convergence at the proved metric laws removes the abstract
`RatToleranceCloseLaws` hypothesis: for any nonnegative, monotone non-increasing
rational sequence with an explicit null-modulus, the alternating partial sums
form a regular Cauchy sequence and converge to a genuine located real. No
abstract metric assumption, no axioms.
-/

namespace BEDC.Derived.RHRoute.AltConvergence

open BEDC.Derived.LocatedReal

/-- The alternating partial sums (over the grounded dyadic-tolerance metric) are
a regular Cauchy sequence of located reals. -/
def groundedAltCauchy (D : RatLeibnizData) :
    LRealSeqCauchy (altSeqLReal groundedRatToleranceLaws D) :=
  rat_alt_partial_cauchy groundedRatToleranceLaws D

/-- The genuine located-real limit of the alternating series, in the grounded
metric. Unconditional alternating series test. -/
def groundedAltLimit (D : RatLeibnizData) :
    LReal (RatToleranceMetricKit groundedRatToleranceLaws) :=
  altLimit groundedRatToleranceLaws D

end BEDC.Derived.RHRoute.AltConvergence

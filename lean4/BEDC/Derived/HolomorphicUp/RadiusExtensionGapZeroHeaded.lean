import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem HolomorphicOpenDisk_radius_extension_gap_zero_headed_absurd
    {center radius radius' point gap extra w : BHist} :
    HolomorphicOpenDisk center radius point gap -> UnaryHistory extra ->
      Cont radius extra radius' -> append gap extra = BHist.e0 w -> False := by
  intro disk extraUnary radiusStep zeroHeaded
  have extended : HolomorphicOpenDisk center radius' point (append gap extra) :=
    HolomorphicOpenDisk_radius_extension_closed disk extraUnary radiusStep
  have extendedGapUnary : UnaryHistory (append gap extra) :=
    extended.right.right.right.left
  have zeroUnary : UnaryHistory (BHist.e0 w) :=
    unary_transport extendedGapUnary zeroHeaded
  exact unary_no_zero_extension zeroUnary

end BEDC.Derived.HolomorphicUp

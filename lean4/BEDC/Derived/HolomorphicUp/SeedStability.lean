import BEDC.Derived.HolomorphicUp
import BEDC.Derived.HolomorphicUp.IteratedTransport

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem HolomorphicOpenDisk_stability_certificate_fields
    {center center' radius radius' point point' gap gap' seed seed' iterate iterate' : BHist}
    {n : Nat} :
    HolomorphicOpenDisk center radius point gap ->
      hsame center center' ->
        hsame radius radius' ->
          hsame point point' ->
            hsame gap gap' ->
              IteratedCplxDiff seed n iterate ->
                hsame seed seed' ->
                  hsame iterate iterate' ->
                    HolomorphicOpenDisk center' radius' point' gap' ∧
                      IteratedCplxDiff seed' n iterate' ∧
                        (UnaryHistory seed' -> UnaryHistory iterate') ∧
                          Cont point' gap' radius' := by
  intro disk sameCenter sameRadius samePoint sameGap diff sameSeed sameIterate
  have diskTransport :
      HolomorphicOpenDisk center' radius' point' gap' ∧ UnaryHistory center' ∧
        UnaryHistory radius' ∧ UnaryHistory point' ∧ UnaryHistory gap' ∧
          Cont point' gap' radius' :=
    HolomorphicOpenDisk_hsame_transport sameCenter sameRadius samePoint sameGap disk
  have diffTransport :
      IteratedCplxDiff seed' n iterate' ∧ (UnaryHistory seed' -> UnaryHistory iterate') :=
    IteratedCplxDiff_hsame_transport_unary_readback sameSeed sameIterate diff
  exact And.intro diskTransport.left
    (And.intro diffTransport.left
      (And.intro diffTransport.right diskTransport.right.right.right.right.right))

end BEDC.Derived.HolomorphicUp

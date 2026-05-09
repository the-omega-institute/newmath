import BEDC.FKernel.Cont.Units
import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem HolomorphicUp_StdBridge {center radius point gap bridge : BHist} :
    HolomorphicOpenDisk center radius point gap -> Cont radius BHist.Empty bridge ->
      HolomorphicOpenDisk center bridge point gap ∧ hsame bridge radius := by
  intro disk bridgeRow
  have bridgeRadius : hsame bridge radius :=
    cont_right_unit_result bridgeRow
  have transported :=
    HolomorphicOpenDisk_hsame_transport (hsame_refl center) (hsame_symm bridgeRadius)
      (hsame_refl point) (hsame_refl gap) disk
  exact And.intro transported.left bridgeRadius

end BEDC.Derived.HolomorphicUp

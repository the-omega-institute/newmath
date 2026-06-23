import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicMeshDiameterUp : Type where
  | mk (mesh endpointRows diameterLedger refinement transport replay provenance name : BHist) :
      DyadicMeshDiameterUp
  deriving DecidableEq

def dyadicMeshDiameterFields : DyadicMeshDiameterUp → List BHist
  | DyadicMeshDiameterUp.mk M E D R H C P N => [M, E, D, R, H, C, P, N]

theorem dyadicMeshDiameterFields_mk
    (M E D R H C P N : BHist) :
    dyadicMeshDiameterFields (DyadicMeshDiameterUp.mk M E D R H C P N) =
      [M, E, D, R, H, C, P, N] := by
  rfl

end BEDC.Derived

import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ConvRadSourceSpec_public_boundary_exactness {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadSourceSpec a z0 R ->
      SemanticNameCert (ConvRad a) (ConvRad a) (ConvRad a) hsame ∧
        ConvRadCheckedRowReduct a z0 R := by
  intro source
  exact And.intro
    (ConvRad_semanticNameCert source.right)
    (ConvRadSourceSpec_checkedRowReduct_readback source)

end BEDC.Derived.ConvergenceRadiusUp

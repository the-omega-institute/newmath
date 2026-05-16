import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRoutePublicFactorization
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (hK :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg) :
    hsame (append (append (append dyadic windows) readback) sealRow)
        (append (append (append dyadic windows) readback) sealRow) ∧
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  exact ⟨hsame_refl (append (append (append dyadic windows) readback) sealRow), hK⟩

end BEDC.Derived.DiagonallimitcompatibilityUp

import BEDC.Derived.CoveringdimensionUp.FiniteCoverRootCarrier
import BEDC.FKernel.Cont

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverRealSeparabilitySimplicialLock [AskSetup] [PackageSetup]
    {K C A M D Q G H T P N densityRead nerveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverRootCarrier K C A M D Q G H T P N bundle pkg →
      Cont M A densityRead →
        Cont M D nerveRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              UnaryHistory K ∧ UnaryHistory C ∧ UnaryHistory A ∧ UnaryHistory M ∧
                UnaryHistory D ∧ UnaryHistory densityRead ∧ UnaryHistory nerveRead ∧
                  Cont M A densityRead ∧ Cont M D nerveRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteCoverRootCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier densityRoute nerveRoute provenancePkg localNamePkg
  obtain ⟨kUnary, cUnary, aUnary, mUnary, dUnary, _qUnary, _gUnary, _hUnary,
    _tUnary, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed mUnary aUnary densityRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed mUnary dUnary nerveRoute
  exact
    ⟨kUnary, cUnary, aUnary, mUnary, dUnary, densityUnary, nerveUnary, densityRoute,
      nerveRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.CoveringdimensionUp

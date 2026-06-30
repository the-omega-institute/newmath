import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameOpenPhaseFiniteWindowExitDeterminacy [AskSetup] [PackageSetup]
    {window readback dyadic realSeal transport _route provenance _name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window ->
      UnaryHistory readback ->
        UnaryHistory dyadic ->
          UnaryHistory realSeal ->
            Cont window dyadic readback ->
              Cont readback realSeal endpoint ->
                hsame transport (append window dyadic) ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle endpoint pkg ->
                      UnaryHistory endpoint ∧ Cont window dyadic readback ∧
                        Cont readback realSeal endpoint ∧
                          hsame transport (append window dyadic) ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro _windowUnary readbackUnary _dyadicUnary realSealUnary windowRoute endpointRoute
    transportSame provenancePkg endpointPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary endpointRoute
  exact
    ⟨endpointUnary, windowRoute, endpointRoute, transportSame, provenancePkg, endpointPkg⟩

end BEDC.Derived.StreamNameUp

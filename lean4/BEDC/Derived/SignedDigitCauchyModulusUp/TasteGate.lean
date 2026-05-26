import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDigitCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SignedDigitCauchyModulusCarrier [AskSetup] [PackageSetup]
    (S W E T R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧
    UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      PkgSig bundle P pkg ∧ UnaryHistory N

theorem SignedDigitCauchyModulusNameCertObligations [AskSetup] [PackageSetup]
    {S W E T R L H C P N normalized thresholdRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitCauchyModulusCarrier S W E T R L H C P N bundle pkg ->
      Cont S W normalized ->
        Cont normalized E thresholdRead ->
          Cont thresholdRead T regularRead ->
            Cont regularRead L sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory normalized ∧ UnaryHistory thresholdRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ Cont S W normalized ∧
                    Cont normalized E thresholdRead ∧ Cont thresholdRead T regularRead ∧
                      Cont regularRead L sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceWindowNormalized normalizedEndpointThreshold thresholdRegularRead
    regularSealRead sealPkg
  obtain ⟨sourceUnary, windowUnary, endpointUnary, thresholdUnary, _regularUnary, sealUnary,
    _transportUnary, _routeUnary, provenancePkg, _nameUnary⟩ := carrier
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed sourceUnary windowUnary sourceWindowNormalized
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed normalizedUnary endpointUnary normalizedEndpointThreshold
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed thresholdReadUnary thresholdUnary thresholdRegularRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary sealUnary regularSealRead
  exact
    ⟨normalizedUnary, thresholdReadUnary, regularReadUnary, sealReadUnary,
      sourceWindowNormalized, normalizedEndpointThreshold, thresholdRegularRead, regularSealRead,
      provenancePkg, sealPkg⟩

end BEDC.Derived.SignedDigitCauchyModulusUp

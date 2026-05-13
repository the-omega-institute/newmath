import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RealCompletenessUp finite carrier.
-/

namespace BEDC.Derived.RealCompletenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCompletenessBHistCarrier [AskSetup] [PackageSetup]
    (family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory selector ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem RealCompletenessBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback «seal» transport
        route provenance cert endpoint bundle pkg ->
      UnaryHistory family /\ UnaryHistory modulus /\ UnaryHistory selector /\
        UnaryHistory dyadic /\ UnaryHistory windows /\ UnaryHistory readback /\ UnaryHistory «seal» /\
          UnaryHistory transport /\ UnaryHistory route /\ UnaryHistory provenance /\
            UnaryHistory cert /\ UnaryHistory endpoint /\ Cont transport route endpoint /\
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩ := carrier
  exact ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩

end BEDC.Derived.RealCompletenessUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailSelectorCarrier [AskSetup] [PackageSetup]
    (precision stream regularity dyadic realSeal tailWitness transports routes provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
    UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont regularity dyadic tailWitness ∧ Cont tailWitness routes provenance ∧
          Cont realSeal provenance localCert ∧ PkgSig bundle provenance pkg

theorem RegularCauchyTailSelectorCarrier_precision_window_exactness [AskSetup]
    [PackageSetup]
    {precision stream regularity dyadic realSeal tailWitness transports routes provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorCarrier precision stream regularity dyadic realSeal tailWitness
        transports routes provenance localCert bundle pkg ->
      Cont tailWitness routes consumer ->
        UnaryHistory precision ∧ UnaryHistory tailWitness ∧ UnaryHistory consumer ∧
          Cont regularity dyadic tailWitness ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  obtain ⟨precisionUnary, _streamUnary, regularityUnary, dyadicUnary, _realSealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, tailWitnessRoute,
    _provenanceRoute, _localCertRoute, pkgSig⟩ := carrier
  have tailWitnessUnary : UnaryHistory tailWitness :=
    unary_cont_closed regularityUnary dyadicUnary tailWitnessRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tailWitnessUnary routesUnary consumerRoute
  exact ⟨precisionUnary, tailWitnessUnary, consumerUnary, tailWitnessRoute, pkgSig⟩

end BEDC.Derived.RegularCauchyTailSelectorUp

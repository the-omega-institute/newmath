import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LargeModelInscriptionPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LargeModelInscriptionPointCarrier [AskSetup] [PackageSetup]
    (model activation corpus output refusal transport route provenance name read : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  UnaryHistory model ∧ UnaryHistory activation ∧ UnaryHistory corpus ∧
    UnaryHistory output ∧ UnaryHistory refusal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        UnaryHistory read ∧ Cont model activation transport ∧ Cont corpus output route ∧
          Cont transport route provenance ∧ hsame route read ∧ PkgSig bundle read pkg

theorem LargeModelInscriptionPointCarrier_source_channel_exactness [AskSetup] [PackageSetup]
    {model activation corpus output refusal transport route provenance name read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LargeModelInscriptionPointCarrier model activation corpus output refusal transport route
        provenance name read bundle pkg ->
      Cont corpus output read ->
        PkgSig bundle read pkg ->
          UnaryHistory corpus ∧ UnaryHistory output ∧ Cont corpus output read ∧
            PkgSig bundle read pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro hCarrier _corpusOutputRead _readPkg
  obtain ⟨_modelUnary, _activationUnary, corpusUnary, outputUnary, _refusalUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _readUnary,
    _modelActivationTransport, corpusOutputRoute, _transportRouteProvenance,
    routeReadback, carrierPkg⟩ := hCarrier
  have corpusOutputReadFromCarrier : Cont corpus output read :=
    hsame_trans (hsame_symm routeReadback) corpusOutputRoute
  exact And.intro corpusUnary
    (And.intro outputUnary
      (And.intro corpusOutputReadFromCarrier carrierPkg))

end BEDC.Derived.LargeModelInscriptionPointUp

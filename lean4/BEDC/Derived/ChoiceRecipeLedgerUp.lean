import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceRecipeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ChoiceRecipeLedgerCertificate [AskSetup] [PackageSetup]
    (term recipes requested refusal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory term ∧ UnaryHistory recipes ∧ UnaryHistory requested ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont term recipes requested ∧
        Cont requested refusal transport ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg

theorem ChoiceRecipeLedgerNonEscape [AskSetup] [PackageSetup]
    {term recipes requested refusal transport replay provenance localName
      requestedRefusalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCertificate term recipes requested refusal transport replay provenance
        localName bundle pkg →
      Cont requested refusal requestedRefusalRoute →
        UnaryHistory term ∧ UnaryHistory recipes ∧ UnaryHistory requested ∧
          UnaryHistory refusal ∧ UnaryHistory requestedRefusalRoute ∧
            Cont requested refusal requestedRefusalRoute ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro certificate requestedRefusalCont
  rcases certificate with
    ⟨termUnary, recipesUnary, requestedUnary, refusalUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, _termRecipesRequested, _requestedRefusalTransport,
      _transportReplayProvenance, provenancePkg⟩
  have routeUnary : UnaryHistory requestedRefusalRoute :=
    unary_cont_closed requestedUnary refusalUnary requestedRefusalCont
  exact
    ⟨termUnary, recipesUnary, requestedUnary, refusalUnary, routeUnary,
      requestedRefusalCont, provenancePkg⟩

end BEDC.Derived.ChoiceRecipeLedgerUp

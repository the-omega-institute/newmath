import BEDC.Derived.ForbiddenAxiomAncestryUp

namespace BEDC.Derived.ForbiddenAxiomAncestryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ForbiddenAxiomAncestryCarrier_refusal_determinacy [AskSetup] [PackageSetup]
    {theoremRow ancestry forbidden verdict verdict' transports transports' routes provenance
      provenance' nameRow nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
        provenance nameRow bundle pkg ->
      ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict' transports' routes
        provenance' nameRow' bundle pkg ->
        hsame verdict verdict' := by
  intro left right
  obtain
    ⟨_theoremUnary, _ancestryUnary, _forbiddenUnary, _verdictUnary, _transportsUnary,
      _routesUnary, _provenanceUnary, _nameRowUnary, verdictComparison,
      _theoremAncestry, _transportProvenance, _provenancePkg⟩ := left
  obtain
    ⟨_theoremUnary', _ancestryUnary', _forbiddenUnary', _verdictUnary',
      _transportsUnary', _routesUnary', _provenanceUnary', _nameRowUnary',
      verdictComparison', _theoremAncestry', _transportProvenance', _provenancePkg'⟩ :=
        right
  exact hsame_trans verdictComparison (hsame_symm verdictComparison')

end BEDC.Derived.ForbiddenAxiomAncestryUp

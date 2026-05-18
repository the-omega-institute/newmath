import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceRecipeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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


def ChoiceRecipeLedgerCarrier [AskSetup] [PackageSetup]
    (request recipes output refusal transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont request recipes output ∧ Cont output refusal route ∧
          Cont route transport provenance ∧ PkgSig bundle localName pkg

theorem ChoiceRecipeLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont provenance localName obligationRead →
        PkgSig bundle obligationRead pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
            UnaryHistory refusal ∧ UnaryHistory provenance ∧ UnaryHistory obligationRead ∧
              Cont request recipes output ∧ Cont output refusal route ∧
                Cont route transport provenance ∧ Cont provenance localName obligationRead ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle obligationRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist =>
                        ChoiceRecipeLedgerCarrier request recipes output refusal transport route
                            provenance localName bundle pkg ∧
                          hsame row obligationRead)
                      (fun row : BHist =>
                        Cont request recipes output ∧ Cont output refusal route ∧
                          Cont route transport provenance ∧
                            Cont provenance localName row ∧ PkgSig bundle obligationRead pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligationRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier provenanceLocalName obligationReadPkg
  obtain ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, transportUnary, routeUnary,
    provenanceUnary, localNameUnary, requestRecipesOutput, outputRefusalRoute,
    routeTransportProvenance, localNamePkg⟩ := carrier
  have carrierWitness :
      ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance
          localName bundle pkg :=
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, transportUnary, routeUnary,
      provenanceUnary, localNameUnary, requestRecipesOutput, outputRefusalRoute,
      routeTransportProvenance, localNamePkg⟩
  have obligationReadUnary : UnaryHistory obligationRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalName
  have nameCert :
      SemanticNameCert
        (fun row : BHist =>
          ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance
              localName bundle pkg ∧
            hsame row obligationRead)
        (fun row : BHist =>
          Cont request recipes output ∧ Cont output refusal route ∧
            Cont route transport provenance ∧
              Cont provenance localName row ∧ PkgSig bundle obligationRead pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligationRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead (And.intro carrierWitness (hsame_refl obligationRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨requestRecipesOutput, outputRefusalRoute, routeTransportProvenance,
          cont_result_hsame_transport provenanceLocalName (hsame_symm source.right),
          obligationReadPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport obligationReadUnary (hsame_symm source.right), obligationReadPkg⟩
  }
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, provenanceUnary,
      obligationReadUnary, requestRecipesOutput, outputRefusalRoute, routeTransportProvenance,
      provenanceLocalName, localNamePkg, obligationReadPkg, nameCert⟩

theorem ChoiceRecipeLedgerCarrier_finite_recipe_coverage [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont recipes refusal coverageRead →
        PkgSig bundle coverageRead pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory coverageRead ∧
            Cont request recipes output ∧ Cont recipes refusal coverageRead ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle coverageRead pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row recipes ∨ hsame row coverageRead)
                  (fun row : BHist => PkgSig bundle coverageRead pkg ∧ hsame row coverageRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier recipesRefusalCoverage coverageReadPkg
  obtain ⟨requestUnary, recipesUnary, _outputUnary, refusalUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, requestRecipesOutput, _outputRefusalRoute,
    _routeTransportProvenance, localNamePkg⟩ := carrier
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed recipesUnary refusalUnary recipesRefusalCoverage
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row recipes ∨ hsame row coverageRead)
        (fun row : BHist => PkgSig bundle coverageRead pkg ∧ hsame row coverageRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro coverageRead ⟨hsame_refl coverageRead, coverageReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨coverageReadPkg, source.left⟩
    }
  exact
    ⟨requestUnary, recipesUnary, coverageReadUnary, requestRecipesOutput,
      recipesRefusalCoverage, localNamePkg, coverageReadPkg, cert⟩

theorem ChoiceRecipeLedgerCarrier_term_stratum_handoff [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont localName request handoff →
        PkgSig bundle handoff pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
            UnaryHistory refusal ∧ UnaryHistory handoff ∧ Cont request recipes output ∧
              Cont output refusal route ∧ Cont localName request handoff ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier localNameRequest handoffPkg
  obtain ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, _transportUnary, _routeUnary,
    _provenanceUnary, localNameUnary, requestRecipesOutput, outputRefusalRoute,
    _routeTransportProvenance, localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed localNameUnary requestUnary localNameRequest
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, handoffUnary, requestRecipesOutput,
      outputRefusalRoute, localNameRequest, localNamePkg, handoffPkg⟩

theorem ChoiceRecipeLedgerTermStratumHandoff [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont request output handoffRead →
        UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
          UnaryHistory refusal ∧ UnaryHistory handoffRead ∧ Cont request recipes output ∧
            Cont request output handoffRead ∧ Cont output refusal route ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier requestOutputHandoff
  rcases carrier with
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _localNameUnary, requestRecipesOutput, outputRefusalRoute,
      _routeTransportProvenance, localNamePkg⟩
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed requestUnary outputUnary requestOutputHandoff
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, handoffUnary,
      requestRecipesOutput, requestOutputHandoff, outputRefusalRoute, localNamePkg⟩

theorem ChoiceRecipeLedgerEffectiveReplacementBoundary [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName replacement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance
        localName bundle pkg →
      Cont output refusal replacement →
        PkgSig bundle replacement pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
            UnaryHistory refusal ∧ UnaryHistory replacement ∧ Cont request recipes output ∧
              Cont output refusal route ∧ Cont output refusal replacement ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle replacement pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier outputRefusalReplacement replacementPkg
  rcases carrier with
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _localNameUnary, requestRecipesOutput, outputRefusalRoute,
      _routeTransportProvenance, localNamePkg⟩
  have replacementUnary : UnaryHistory replacement :=
    unary_cont_closed outputUnary refusalUnary outputRefusalReplacement
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, replacementUnary,
      requestRecipesOutput, outputRefusalRoute, outputRefusalReplacement, localNamePkg,
      replacementPkg⟩

theorem ChoiceRecipeLedgerCarrier_refusal_route_determinacy [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont output refusal refusalRead →
        PkgSig bundle refusalRead pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
            UnaryHistory refusal ∧ UnaryHistory refusalRead ∧ Cont request recipes output ∧
              Cont output refusal route ∧ Cont output refusal refusalRead ∧
                hsame refusalRead route ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier outputRefusalRead refusalReadPkg
  rcases carrier with
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _localNameUnary, requestRecipesOutput, outputRefusalRoute,
      _routeTransportProvenance, localNamePkg⟩
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed outputUnary refusalUnary outputRefusalRead
  have refusalReadSameRoute : hsame refusalRead route :=
    cont_deterministic outputRefusalRead outputRefusalRoute
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, refusalReadUnary,
      requestRecipesOutput, outputRefusalRoute, outputRefusalRead, refusalReadSameRoute,
      localNamePkg, refusalReadPkg⟩

end BEDC.Derived.ChoiceRecipeLedgerUp

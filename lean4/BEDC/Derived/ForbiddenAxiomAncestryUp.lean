import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ForbiddenAxiomAncestryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ForbiddenAxiomAncestryCarrier [AskSetup] [PackageSetup]
    (theoremRow ancestry forbidden verdict transports routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory theoremRow ∧ UnaryHistory ancestry ∧ UnaryHistory forbidden ∧
    UnaryHistory verdict ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        hsame verdict (append ancestry forbidden) ∧
          Cont theoremRow ancestry transports ∧
            Cont transports routes provenance ∧ PkgSig bundle provenance pkg

theorem ForbiddenAxiomAncestryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {theoremRow ancestry forbidden verdict transports routes provenance nameRow
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
        provenance nameRow bundle pkg ->
      Cont routes nameRow auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row nameRow ∧
                  ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports
                    routes provenance nameRow bundle pkg)
              (fun row : BHist => hsame row nameRow)
              (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory theoremRow ∧ UnaryHistory ancestry ∧ UnaryHistory forbidden ∧
              UnaryHistory verdict ∧ UnaryHistory auditRead ∧
                hsame verdict (append ancestry forbidden) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier auditRoute auditPkg
  have carrierPacket := carrier
  obtain ⟨theoremUnary, ancestryUnary, forbiddenUnary, verdictUnary, _transportsUnary,
    routesUnary, _provenanceUnary, nameRowUnary, verdictComparison, _theoremAncestry,
    _transportProvenance, provenancePkg⟩ := carrierPacket
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed routesUnary nameRowUnary auditRoute
  have sourceAtName :
      (fun row : BHist =>
        hsame row nameRow ∧
          ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
            provenance nameRow bundle pkg)
          nameRow :=
    And.intro (hsame_refl nameRow) carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row nameRow ∧
            ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
              provenance nameRow bundle pkg)
        (fun row : BHist => hsame row nameRow)
        (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRow sourceAtName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    And.intro cert
      (And.intro theoremUnary
        (And.intro ancestryUnary
          (And.intro forbiddenUnary
            (And.intro verdictUnary
              (And.intro auditReadUnary
                (And.intro verdictComparison
                  (And.intro provenancePkg auditPkg)))))))

theorem ForbiddenAxiomAncestryCarrier_comparison_exactness [AskSetup] [PackageSetup]
    {theoremRow ancestry forbidden verdict transports routes provenance nameRow
      compareRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
        provenance nameRow bundle pkg ->
      Cont verdict routes compareRead ->
        PkgSig bundle compareRead pkg ->
          UnaryHistory ancestry ∧ UnaryHistory forbidden ∧ UnaryHistory verdict ∧
            UnaryHistory routes ∧ UnaryHistory compareRead ∧
              hsame verdict (append ancestry forbidden) ∧
                Cont verdict routes compareRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle compareRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory hsame
  intro carrier comparisonRoute comparisonPkg
  obtain ⟨_theoremUnary, ancestryUnary, forbiddenUnary, verdictUnary, _transportsUnary,
    routesUnary, _provenanceUnary, _nameRowUnary, verdictComparison, _theoremAncestry,
      _transportProvenance, provenancePkg⟩ := carrier
  have compareReadUnary : UnaryHistory compareRead :=
    unary_cont_closed verdictUnary routesUnary comparisonRoute
  exact
    ⟨ancestryUnary, forbiddenUnary, verdictUnary, routesUnary, compareReadUnary,
      verdictComparison, comparisonRoute, provenancePkg, comparisonPkg⟩

theorem ForbiddenAxiomAncestryCarrier_transport_replay [AskSetup] [PackageSetup]
    {theoremRow ancestry forbidden verdict transports routes provenance nameRow
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ForbiddenAxiomAncestryCarrier theoremRow ancestry forbidden verdict transports routes
        provenance nameRow bundle pkg ->
      Cont transports routes replayRead ->
        PkgSig bundle replayRead pkg ->
          UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory replayRead ∧
            hsame verdict (append ancestry forbidden) ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory hsame
  intro carrier replayRoute replayPkg
  obtain ⟨_theoremUnary, _ancestryUnary, _forbiddenUnary, _verdictUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameRowUnary, verdictComparison,
      _theoremAncestry, _transportProvenance, provenancePkg⟩ := carrier
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportsUnary routesUnary replayRoute
  exact
    ⟨transportsUnary, routesUnary, replayReadUnary, verdictComparison, provenancePkg,
      replayPkg⟩

end BEDC.Derived.ForbiddenAxiomAncestryUp

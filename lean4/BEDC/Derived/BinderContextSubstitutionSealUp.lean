import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BinderContextSubstitutionSealCarrier [AskSetup] [PackageSetup]
    (term depth payload result boundary transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  UnaryHistory term ∧ UnaryHistory depth ∧ UnaryHistory payload ∧ UnaryHistory result ∧
    UnaryHistory boundary ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont term depth result ∧ hsame boundary BHist.Empty ∧
          Cont payload result transport ∧ Cont transport boundary route ∧
            hsame provenance result ∧ PkgSig bundle result pkg

theorem BinderContextSubstitutionSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg ->
      Cont result boundary endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                BinderContextSubstitutionSealCarrier term depth payload result boundary
                  transport route provenance name bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row result)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory term ∧ UnaryHistory depth ∧ UnaryHistory payload ∧
              UnaryHistory result ∧ UnaryHistory endpoint ∧ Cont term depth result ∧
                Cont result boundary endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert
  intro hCarrier endpointRoute endpointPkg
  have carrierPacket := hCarrier
  obtain ⟨termUnary, depthUnary, payloadUnary, resultUnary, boundaryUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, termDepthResult, boundaryEmpty,
    _payloadResultTransport, _transportBoundaryRoute, provenanceResult, _carrierPkg⟩ :=
    carrierPacket
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed resultUnary boundaryUnary endpointRoute
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic endpointRoute (cont_right_unit result)
  have endpointProvenance : hsame endpoint provenance :=
    hsame_trans endpointResult (hsame_symm provenanceResult)
  have sourceAtEndpoint :
      (fun row : BHist =>
        BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
            provenance name bundle pkg ∧ hsame row endpoint) endpoint :=
    And.intro hCarrier (hsame_refl endpoint)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
              provenance name bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row result)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact hsame_trans sourceRow.right endpointResult
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.right endpointProvenance) endpointPkg
  }
  exact
    And.intro cert
      (And.intro termUnary
        (And.intro depthUnary
          (And.intro payloadUnary
            (And.intro resultUnary
              (And.intro endpointUnary
                (And.intro termDepthResult endpointRoute))))))

theorem BinderContextSubstitutionSealCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg ->
      Cont result boundary endpoint ->
        PkgSig bundle endpoint pkg ->
          hsame endpoint result ∧ UnaryHistory endpoint ∧ Cont term depth result ∧
            Cont result boundary endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro hCarrier endpointRoute endpointPkg
  obtain ⟨_termUnary, _depthUnary, _payloadUnary, resultUnary, boundaryUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, termDepthResult,
    boundaryEmpty, _payloadResultTransport, _transportBoundaryRoute, _provenanceResult,
    _carrierPkg⟩ := hCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed resultUnary boundaryUnary endpointRoute
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic endpointRoute (cont_right_unit result)
  exact
    ⟨endpointResult, endpointUnary, termDepthResult, endpointRoute, endpointPkg⟩

end BEDC.Derived.BinderContextSubstitutionSealUp

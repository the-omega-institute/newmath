import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatedRealFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedRealFunctionRoute [AskSetup] [PackageSetup]
    (interval approximation tail uniformRoute endpointSeal route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory interval ∧ UnaryHistory approximation ∧ UnaryHistory tail ∧
    UnaryHistory uniformRoute ∧ UnaryHistory endpointSeal ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ Cont interval approximation tail ∧
        Cont tail uniformRoute endpointSeal ∧ Cont endpointSeal route provenance ∧
          Cont route provenance localCert ∧ PkgSig bundle provenance pkg

theorem RegulatedRealFunction_integration_facing_handoff_boundary [AskSetup]
    [PackageSetup]
    {interval approximation tail uniformRoute endpointSeal route provenance localCert
      integrationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedRealFunctionRoute interval approximation tail uniformRoute endpointSeal route
        provenance localCert bundle pkg →
      Cont endpointSeal route integrationRead →
        PkgSig bundle integrationRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegulatedRealFunctionRoute interval approximation tail uniformRoute
                    endpointSeal route provenance localCert bundle pkg ∧
                  hsame row localCert)
              (fun row : BHist =>
                RegulatedRealFunctionRoute interval approximation tail uniformRoute
                    endpointSeal route provenance localCert bundle pkg ∧
                  hsame row localCert)
              (fun row : BHist =>
                RegulatedRealFunctionRoute interval approximation tail uniformRoute
                    endpointSeal route provenance localCert bundle pkg ∧
                  hsame row localCert)
              hsame ∧
            UnaryHistory integrationRead ∧ Cont interval approximation tail ∧
              Cont tail uniformRoute endpointSeal ∧ Cont endpointSeal route integrationRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle integrationRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg SemanticNameCert hsame
  intro routeRows endpointRoute integrationPkg
  have routeRowsCopy := routeRows
  obtain ⟨_intervalUnary, _approximationUnary, _tailUnary, _uniformUnary,
    endpointUnary, routeUnary, _provenanceUnary, _localCertUnary, intervalApproxTail,
    tailUniformEndpoint, _endpointRouteProvenance, _routeProvenanceLocal,
    provenancePkg⟩ := routeRows
  have integrationUnary : UnaryHistory integrationRead :=
    unary_cont_closed endpointUnary routeUnary endpointRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          RegulatedRealFunctionRoute interval approximation tail uniformRoute endpointSeal
              route provenance localCert bundle pkg ∧
            hsame row localCert)
        (fun row : BHist =>
          RegulatedRealFunctionRoute interval approximation tail uniformRoute endpointSeal
              route provenance localCert bundle pkg ∧
            hsame row localCert)
        (fun row : BHist =>
          RegulatedRealFunctionRoute interval approximation tail uniformRoute endpointSeal
              route provenance localCert bundle pkg ∧
            hsame row localCert)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localCert (And.intro routeRowsCopy (hsame_refl localCert))
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, integrationUnary, intervalApproxTail, tailUniformEndpoint, endpointRoute,
      provenancePkg, integrationPkg⟩

end BEDC.Derived.RegulatedRealFunctionUp

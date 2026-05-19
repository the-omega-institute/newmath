import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRouteLedger_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      routeLedger routeEndpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle routeLedger ->
        Cont routeLedger dyadic routeEndpoint ->
          Cont routeEndpoint windows consumer ->
            PkgSig bundle consumer pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                  (fun row : BHist => hsame row consumer ∧
                    Cont diagonal triangle routeLedger ∧ Cont routeLedger dyadic routeEndpoint)
                  (fun row : BHist => hsame row consumer ∧
                    Cont routeEndpoint windows consumer)
                  hsame ∧
                UnaryHistory routeLedger ∧ UnaryHistory routeEndpoint ∧
                  UnaryHistory consumer ∧ Cont diagonal triangle routeLedger ∧
                    Cont routeLedger dyadic routeEndpoint ∧
                      Cont routeEndpoint windows consumer ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro carrier diagonalTriangleLedger ledgerDyadicEndpoint endpointWindowsConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have routeLedgerUnary : UnaryHistory routeLedger :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleLedger
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_cont_closed routeLedgerUnary dyadicUnary ledgerDyadicEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeEndpointUnary windowsUnary endpointWindowsConsumer
  have semanticCert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist => hsame row consumer ∧ Cont diagonal triangle routeLedger ∧
          Cont routeLedger dyadic routeEndpoint)
        (fun row : BHist => hsame row consumer ∧ Cont routeEndpoint windows consumer)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer
        (And.intro (hsame_refl consumer) consumerUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left)
          (unary_transport sourceRow.right same)
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left
        (And.intro diagonalTriangleLedger ledgerDyadicEndpoint)
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left endpointWindowsConsumer
  }
  exact
    ⟨semanticCert, routeLedgerUnary, routeEndpointUnary, consumerUnary,
      diagonalTriangleLedger, ledgerDyadicEndpoint, endpointWindowsConsumer, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp

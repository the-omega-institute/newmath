import BEDC.Derived.ArchimedeanRealUp

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanRealCauchyThresholdForwardRoute [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont boundLedger routes cauchyRead ->
        PkgSig bundle cauchyRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
              (fun row : BHist => Cont boundLedger routes row ∧ PkgSig bundle cauchyRead pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle cauchyRead pkg)
              hsame ∧
            UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧ UnaryHistory streamWindow ∧
              UnaryHistory regseqHandoff ∧ UnaryHistory boundLedger ∧
                UnaryHistory cauchyRead := by
  -- BEDC touchpoint anchor: ArchimedeanRealCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier boundLedgerRoutesCauchy cauchyPkg
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    regseqHandoffUnary, boundLedgerUnary, _transportUnary, routesUnary, _provenanceUnary,
    _localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed boundLedgerUnary routesUnary boundLedgerRoutesCauchy
  have sourceCauchy :
      (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row) cauchyRead :=
    ⟨hsame_refl cauchyRead, cauchyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist => Cont boundLedger routes row ∧ PkgSig bundle cauchyRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle cauchyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead sourceCauchy
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport boundLedgerRoutesCauchy (hsame_symm source.left),
          cauchyPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cauchyPkg⟩
  }
  exact
    ⟨cert, ratBoundUnary, dyadicBoundUnary, streamWindowUnary, regseqHandoffUnary,
      boundLedgerUnary, cauchyUnary⟩

end BEDC.Derived.ArchimedeanRealUp

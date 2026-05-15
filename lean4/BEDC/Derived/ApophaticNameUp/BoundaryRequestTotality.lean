import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_request_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont request gate requestRead ->
        PkgSig bundle requestRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row request)
              (fun row : BHist =>
                hsame row request ∧ UnaryHistory row ∧ Cont request gate requestRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
                  hsame row request ∧ Cont request gate requestRead)
              hsame ∧
            UnaryHistory request ∧ UnaryHistory requestRead ∧
              Cont request gate requestRead ∧ PkgSig bundle requestRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier requestGateRead requestReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have sourceRequest :
      (fun row : BHist =>
        ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
          bundle pkg ∧ hsame row request) request := by
    exact ⟨carrierPacket, hsame_refl request⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row request)
          (fun row : BHist =>
            hsame row request ∧ UnaryHistory row ∧ Cont request gate requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
              hsame row request ∧ Cont request gate requestRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro request sourceRequest
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right),
            requestGateRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, requestReadPkg, source.right, requestGateRead⟩
    }
  exact ⟨cert, requestUnary, requestReadUnary, requestGateRead, requestReadPkg⟩

end BEDC.Derived.ApophaticNameUp

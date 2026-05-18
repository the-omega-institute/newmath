import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_request_ledger_classifier_exhaustion
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont ledger nameRow boundaryRead ->
        PkgSig bundle boundaryRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row ledger ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                    bundle pkg)
              (fun row : BHist =>
                hsame row ledger ∧ hsame ledger (append request gate) ∧
                  Cont socket request gate ∧ Cont gate ledger nameRow)
              (fun row : BHist =>
                hsame row ledger ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle boundaryRead pkg)
              hsame ∧
            UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameBoundary boundaryPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg)
          (fun row : BHist =>
            hsame row ledger ∧ hsame ledger (append request gate) ∧
              Cont socket request gate ∧ Cont gate ledger nameRow)
          (fun row : BHist =>
            hsame row ledger ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle boundaryRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨hsame_refl ledger, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro row source
      exact ⟨source.left, ledgerSameRequestGate, socketRequestGate, gateLedgerNameRow⟩
    · intro row source
      exact ⟨source.left, provenancePkg, boundaryPkg⟩
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBoundary
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.ApophaticNameUp

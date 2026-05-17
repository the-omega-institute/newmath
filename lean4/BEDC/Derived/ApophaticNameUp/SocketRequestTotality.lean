import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_request_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row socket)
              (fun row : BHist => hsame row socket ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket request gate ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory socketRead ∧
              Cont socket request gate ∧ Cont socket request socketRead ∧
                hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRead socketReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row socket)
          (fun row : BHist => hsame row socket ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request gate ∧ hsame ledger (append request gate) ∧
              PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro socket ⟨carrierPacket, hsame_refl socket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport socketUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨socketRequestGate, ledgerSameRequestGate, provenancePkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, socketReadUnary, socketRequestGate, socketRequestRead,
      ledgerSameRequestGate, provenancePkg, socketReadPkg⟩

end BEDC.Derived.ApophaticNameUp

import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_downstream_socket_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead downstreamRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow socketRead →
        Cont socketRead provenance downstreamRead →
          PkgSig bundle downstreamRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row socket)
                (fun row : BHist => hsame row socket ∧ UnaryHistory row)
                (fun _row : BHist =>
                  Cont socket request gate ∧ Cont ledger nameRow socketRead ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory socketRead ∧ UnaryHistory downstreamRead ∧
                Cont ledger nameRow socketRead ∧
                  Cont socketRead provenance downstreamRead ∧ PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameSocket socketReadProvenance downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameSocket
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed socketReadUnary provenanceUnary socketReadProvenance
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row socket)
          (fun row : BHist => hsame row socket ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont ledger nameRow socketRead ∧
              PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro socket ⟨carrierPacket, hsame_refl socket⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameSocket : hsame row socket := source.right
      exact ⟨rowSameSocket, unary_transport socketUnary (hsame_symm rowSameSocket)⟩
    · intro _row _source
      exact ⟨socketRequestGate, ledgerNameSocket, provenancePkg⟩
  exact
    ⟨cert, socketReadUnary, downstreamUnary, ledgerNameSocket, socketReadProvenance,
      downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp

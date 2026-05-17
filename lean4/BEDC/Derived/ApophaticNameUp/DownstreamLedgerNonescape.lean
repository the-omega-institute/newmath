import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_ledger_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow ledgerRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont ledger nameRow ledgerRead →
        Cont ledgerRead route downstreamRead →
          PkgSig bundle downstreamRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ∧
                  hsame row ledger)
              (fun row : BHist => hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow ledgerRead)
              (fun _row : BHist =>
                Cont ledger nameRow ledgerRead ∧ Cont ledgerRead route downstreamRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
              hsame ∧
            UnaryHistory ledgerRead ∧ UnaryHistory downstreamRead ∧
              Cont ledger nameRow ledgerRead ∧ Cont ledgerRead route downstreamRead ∧
                PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRead ledgerReadRouteDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerReadRouteDownstream
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ∧
            hsame row ledger)
        (fun row : BHist =>
          hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow ledgerRead)
        (fun _row : BHist =>
          Cont ledger nameRow ledgerRead ∧ Cont ledgerRead route downstreamRead ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact
        ⟨source.right, unary_transport ledgerUnary (hsame_symm source.right),
          ledgerNameRead⟩
    · intro _row _source
      exact ⟨ledgerNameRead, ledgerReadRouteDownstream, provenancePkg, downstreamPkg⟩
  exact
    ⟨cert, ledgerReadUnary, downstreamUnary, ledgerNameRead, ledgerReadRouteDownstream,
      downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp

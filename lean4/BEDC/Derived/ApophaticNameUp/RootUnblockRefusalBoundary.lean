import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_unblock_refusal_boundary [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont ledger nameRow downstreamRead →
        PkgSig bundle downstreamRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row ledger)
              (fun row : BHist =>
                hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow downstreamRead)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg ∧
                  hsame ledger (append request gate))
              hsame ∧
            UnaryHistory downstreamRead ∧ hsame ledger (append request gate) ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row ledger)
          (fun row : BHist =>
            hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow downstreamRead)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg ∧
              hsame ledger (append request gate))
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨rowSameLedger, unary_transport ledgerUnary (hsame_symm rowSameLedger),
          ledgerNameDownstream⟩
    · intro _row _source
      exact ⟨provenancePkg, downstreamPkg, ledgerSameRequestGate⟩
  exact ⟨cert, downstreamUnary, ledgerSameRequestGate, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp

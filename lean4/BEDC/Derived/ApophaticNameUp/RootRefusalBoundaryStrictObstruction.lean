import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_boundary_strict_obstruction
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead downstreamRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow rootRead →
        Cont ledger nameRow downstreamRead →
          PkgSig bundle rootRead pkg →
            PkgSig bundle downstreamRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row ledger)
                  (fun row : BHist =>
                    hsame row ledger ∧ Cont socket request gate ∧ Cont gate ledger nameRow)
                  (fun row : BHist => hsame row ledger ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory downstreamRead ∧
                  hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRoot ledgerNameDownstream _rootPkg _downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist =>
            hsame row ledger ∧ Cont socket request gate ∧ Cont gate ledger nameRow)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle provenance pkg)
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
      exact ⟨source.right, socketRequestGate, gateLedgerNameRow⟩
    · intro row source
      exact ⟨source.right, provenancePkg⟩
  exact ⟨cert, rootUnary, downstreamUnary, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp

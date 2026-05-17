import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_gate_ledger_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont gate ledger gateRead →
        Cont ledger nameRow ledgerRead →
          PkgSig bundle gateRead pkg →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route
                        provenance nameRow bundle pkg ∧
                      hsame row ledger)
                  (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                      Cont ledger nameRow ledgerRead)
                  hsame ∧
                UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧ Cont gate ledger gateRead ∧
                  Cont ledger nameRow ledgerRead ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle gateRead pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gateLedgerRead ledgerNameRead gatePkg ledgerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg ∧
              hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              Cont ledger nameRow ledgerRead)
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
      have rowSameLedger : hsame _ ledger := source.right
      constructor
      · exact hsame_trans rowSameLedger ledgerSameRequestGate
      · exact
          unary_transport ledgerUnary
            (hsame_symm rowSameLedger)
    · intro _row _source
      exact ⟨provenancePkg, ledgerPkg, ledgerNameRead⟩
  exact
    ⟨cert, gateReadUnary, ledgerReadUnary, gateLedgerRead, ledgerNameRead,
      ledgerSameRequestGate, gatePkg, ledgerPkg⟩

end BEDC.Derived.ApophaticNameUp

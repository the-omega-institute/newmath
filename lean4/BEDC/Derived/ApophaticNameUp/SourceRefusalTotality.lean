import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_source_refusal_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        PkgSig bundle downstreamRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row socket ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row socket ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  Cont ledger nameRow downstreamRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle downstreamRead pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  Cont ledger nameRow downstreamRead ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRowDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRowDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row socket ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont gate ledger nameRow ∧
              Cont ledger nameRow downstreamRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle downstreamRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro socket ⟨hsame_refl socket, carrierPacket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unary_transport socketUnary (hsame_symm source.left)⟩
      ledger_sound := by
        intro _row _source
        exact
          ⟨socketRequestGate, gateLedgerNameRow, ledgerNameRowDownstream,
            provenancePkg, downstreamPkg⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, downstreamUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameRowDownstream,
      ledgerSameRequestGate, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp

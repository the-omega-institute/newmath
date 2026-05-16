import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_carrier [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg)
          (fun row : BHist => hsame row socket ∧ Cont socket request gate)
          (fun row : BHist => hsame row socket ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory socket ∧
        UnaryHistory request ∧
        UnaryHistory gate ∧
        UnaryHistory ledger ∧
        UnaryHistory transport ∧
        UnaryHistory route ∧
        UnaryHistory provenance ∧
        UnaryHistory nameRow ∧
        Cont socket request gate ∧
        Cont request gate route ∧
        Cont gate ledger nameRow ∧
        hsame ledger (append request gate) ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, _gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row socket ∧ Cont socket request gate)
          (fun row : BHist => hsame row socket ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro socket ⟨hsame_refl socket, carrierPacket⟩
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
        exact ⟨source.left, socketRequestGate⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerNameRow,
      ledgerSameRequestGate, provenancePkg⟩

end BEDC.Derived.ApophaticNameUp

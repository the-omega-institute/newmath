import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameNameCertHandoffExhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow handoffRead
      exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow handoffRead →
        Cont handoffRead route exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row exportRead)
                (fun row : BHist =>
                  Cont ledger nameRow handoffRead ∧ Cont handoffRead route row)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exportRead pkg)
                hsame ∧
              UnaryHistory handoffRead ∧ UnaryHistory exportRead ∧
                Cont ledger nameRow handoffRead ∧ Cont handoffRead route exportRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameHandoff handoffRouteExport exportPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameHandoff
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row exportRead)
          (fun row : BHist =>
            Cont ledger nameRow handoffRead ∧ Cont handoffRead route row)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead
        (And.intro carrierPacket (hsame_refl exportRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨ledgerNameHandoff,
          cont_result_hsame_transport handoffRouteExport (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport exportUnary (hsame_symm source.right), provenancePkg, exportPkg⟩
  }
  exact
    ⟨cert, handoffUnary, exportUnary, ledgerNameHandoff, handoffRouteExport,
      ledgerSameRequestGate, provenancePkg, exportPkg⟩

end BEDC.Derived.ApophaticNameUp

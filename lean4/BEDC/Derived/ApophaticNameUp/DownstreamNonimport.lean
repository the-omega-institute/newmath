import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_nonimport [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow supplyRead downstream
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate supplyRead →
        Cont route provenance downstream →
          Cont downstream nameRow boundary →
            PkgSig bundle supplyRead pkg →
              PkgSig bundle boundary pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg ∧ hsame row downstream)
                    (fun row : BHist =>
                      hsame row downstream ∧ UnaryHistory row ∧
                        Cont route provenance downstream)
                    (fun _row : BHist =>
                      PkgSig bundle supplyRead pkg ∧ PkgSig bundle boundary pkg ∧
                        Cont downstream nameRow boundary)
                    hsame ∧
                  UnaryHistory supplyRead ∧ UnaryHistory downstream ∧
                    UnaryHistory boundary ∧ Cont request gate supplyRead ∧
                      Cont route provenance downstream ∧ Cont downstream nameRow boundary ∧
                        hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier supplyCont downstreamCont boundaryCont supplyPkg boundaryPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed requestUnary gateUnary supplyCont
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routeUnary provenanceUnary downstreamCont
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed downstreamUnary nameRowUnary boundaryCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row downstream)
          (fun row : BHist =>
            hsame row downstream ∧ UnaryHistory row ∧ Cont route provenance downstream)
          (fun _row : BHist =>
            PkgSig bundle supplyRead pkg ∧ PkgSig bundle boundary pkg ∧
              Cont downstream nameRow boundary)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro downstream ⟨carrierPacket, hsame_refl downstream⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport_symm downstreamUnary source.right,
            downstreamCont⟩
      ledger_sound := by
        intro _row _source
        exact ⟨supplyPkg, boundaryPkg, boundaryCont⟩
    }
  exact
    ⟨cert, supplyReadUnary, downstreamUnary, boundaryUnary, supplyCont, downstreamCont,
      boundaryCont, ledgerSameRequestGate, provenancePkg, boundaryPkg⟩

end BEDC.Derived.ApophaticNameUp

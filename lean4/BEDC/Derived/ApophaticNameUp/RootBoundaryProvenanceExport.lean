import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_boundary_provenance_export [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead provenanceRead
      exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow boundaryRead ->
        Cont route provenance provenanceRead ->
          Cont boundaryRead provenanceRead exportRead ->
            PkgSig bundle boundaryRead pkg ->
              PkgSig bundle provenanceRead pkg ->
                PkgSig bundle exportRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row exportRead ∧
                          ApophaticNameCarrier socket request gate ledger transport route
                            provenance nameRow bundle pkg)
                      (fun row : BHist =>
                        hsame row exportRead ∧ Cont boundaryRead provenanceRead exportRead)
                      (fun row : BHist =>
                        hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory provenanceRead ∧
                      UnaryHistory exportRead ∧ hsame ledger (append request gate) ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier boundaryRoute provenanceRoute exportRoute _boundaryPkg _provenanceReadPkg
    exportPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary boundaryRoute
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed routeUnary provenanceUnary provenanceRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed boundaryUnary provenanceReadUnary exportRoute
  have sourceExport :
      (fun row : BHist =>
        hsame row exportRead ∧
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
            bundle pkg) exportRead := by
    exact ⟨hsame_refl exportRead, carrierPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row exportRead ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row exportRead ∧ Cont boundaryRead provenanceRead exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead sourceExport
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
        exact ⟨source.left, exportRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact
    ⟨cert, boundaryUnary, provenanceReadUnary, exportUnary, ledgerSameRequestGate,
      provenancePkg⟩

end BEDC.Derived.ApophaticNameUp

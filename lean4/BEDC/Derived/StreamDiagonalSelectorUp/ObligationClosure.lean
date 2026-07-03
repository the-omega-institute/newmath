import BEDC.Derived.StreamDiagonalSelectorUp

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamDiagonalSelectorPacket_obligation_closure [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint budgetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket
        routes provenance nameCert endpoint bundle pkg ->
      Cont window nameCert budgetRead ->
        Cont endpoint nameCert sealRead ->
          PkgSig bundle budgetRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
                    hsame row readback ∨ hsame row dyadicLedger ∨
                      hsame row diagonalPacket ∨ hsame row endpoint ∨
                        hsame row budgetRead ∨ hsame row sealRead ∨ hsame row nameCert)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont schedule selector window ∧
                    Cont window readback dyadicLedger ∧
                      Cont dyadicLedger diagonalPacket endpoint ∧
                        Cont window nameCert budgetRead ∧ Cont endpoint nameCert sealRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle budgetRead pkg)
                hsame ∧
              UnaryHistory budgetRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet budgetRoute sealRoute budgetPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, nameCertUnary, windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed dyadicLedgerUnary diagonalUnary endpointRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary nameCertUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary nameCertUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
              hsame row readback ∨ hsame row dyadicLedger ∨ hsame row diagonalPacket ∨
                hsame row endpoint ∨ hsame row budgetRead ∨ hsame row sealRead ∨
                  hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont schedule selector window ∧
              Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
                Cont window nameCert budgetRead ∧ Cont endpoint nameCert sealRead ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, ledgerRoute, endpointRoute, budgetRoute, sealRoute,
          endpointPkg, budgetPkg⟩
  }
  exact ⟨cert, budgetUnary, sealUnary⟩

end BEDC.Derived.StreamDiagonalSelectorUp

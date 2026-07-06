import BEDC.Derived.StreamDiagonalSelectorUp

namespace BEDC.Derived.StreamDiagonalSelectorUp.RealSealNonescape

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamDiagonalSelectorPacket_real_seal_nonescape [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      Cont endpoint nameCert sealRead ->
        SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row schedule ∨ hsame row selector ∨ hsame row window ∨ hsame row readback ∨
                hsame row dyadicLedger ∨ hsame row diagonalPacket ∨ hsame row endpoint ∨
                  hsame row sealRead ∨ hsame row nameCert)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont endpoint nameCert sealRead ∧ PkgSig bundle endpoint pkg)
            hsame ∧
          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet sealRoute
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, nameCertUnary, windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed dyadicLedgerUnary diagonalUnary endpointRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary nameCertUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row selector ∨ hsame row window ∨ hsame row readback ∨
              hsame row dyadicLedger ∨ hsame row diagonalPacket ∨ hsame row endpoint ∨
                hsame row sealRead ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint nameCert sealRead ∧ PkgSig bundle endpoint pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, endpointPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.StreamDiagonalSelectorUp.RealSealNonescape

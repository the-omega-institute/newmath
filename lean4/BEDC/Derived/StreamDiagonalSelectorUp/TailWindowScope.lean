import BEDC.Derived.StreamDiagonalSelectorUp

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamDiagonalSelectorPacket_tail_window_scope [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint tailWindow tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      UnaryHistory tailWindow ->
        Cont window tailWindow tailRead ->
          Cont endpoint nameCert sealRead ->
            PkgSig bundle tailWindow pkg ->
              PkgSig bundle tailRead pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row tailRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
                      hsame row readback ∨ hsame row dyadicLedger ∨
                        hsame row diagonalPacket ∨ hsame row tailWindow ∨
                          hsame row tailRead ∨ hsame row sealRead ∨ hsame row nameCert)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont schedule selector window ∧
                      Cont window readback dyadicLedger ∧
                        Cont dyadicLedger diagonalPacket endpoint ∧
                          Cont window tailWindow tailRead ∧
                            Cont endpoint nameCert sealRead ∧
                              PkgSig bundle tailWindow pkg ∧ PkgSig bundle tailRead pkg)
                  hsame ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet tailWindowUnary tailRoute sealRoute tailWindowPkg tailReadPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, nameCertUnary, windowRoute, ledgerRoute, endpointRoute, _endpointPkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed dyadicLedgerUnary diagonalUnary endpointRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary tailWindowUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary nameCertUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row tailRead ∨ hsame row sealRead)
        (fun row : BHist =>
          hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
            hsame row readback ∨ hsame row dyadicLedger ∨ hsame row diagonalPacket ∨
              hsame row tailWindow ∨ hsame row tailRead ∨ hsame row sealRead ∨
                hsame row nameCert)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont schedule selector window ∧
            Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
              Cont window tailWindow tailRead ∧ Cont endpoint nameCert sealRead ∧
                PkgSig bundle tailWindow pkg ∧ PkgSig bundle tailRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead (Or.inl (hsame_refl tailRead))
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
        cases source with
        | inl sameTail =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTail)
        | inr sameSeal =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameTail =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameTail)))))))
      | inr sameSeal =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inl sameSeal))))))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameTail =>
          exact
            ⟨unary_transport tailReadUnary (hsame_symm sameTail), windowRoute, ledgerRoute,
              endpointRoute, tailRoute, sealRoute, tailWindowPkg, tailReadPkg⟩
      | inr sameSeal =>
          exact
            ⟨unary_transport sealReadUnary (hsame_symm sameSeal), windowRoute, ledgerRoute,
              endpointRoute, tailRoute, sealRoute, tailWindowPkg, tailReadPkg⟩
  }
  exact ⟨cert, tailReadUnary, sealReadUnary⟩

end BEDC.Derived.StreamDiagonalSelectorUp

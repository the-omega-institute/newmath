import BEDC.Derived.StreamDiagonalSelectorUp

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamDiagonalSelectorPacket_tail_stability [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint tailWindow tailRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      UnaryHistory tailWindow ->
        Cont window tailWindow tailRead ->
          Cont tailRead diagonalPacket completionRead ->
            PkgSig bundle tailWindow pkg ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
                          hsame row tailWindow ∨ hsame row readback ∨
                            hsame row dyadicLedger ∨ hsame row diagonalPacket ∨
                              hsame row completionRead ∨ hsame row nameCert)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont schedule selector window ∧
                          Cont window readback dyadicLedger ∧
                            Cont dyadicLedger diagonalPacket endpoint ∧
                              Cont window tailWindow tailRead ∧
                                Cont tailRead diagonalPacket completionRead ∧
                                  PkgSig bundle tailWindow pkg ∧
                                    PkgSig bundle tailRead pkg ∧
                                      PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory tailRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet tailWindowUnary tailRoute completionRoute tailWindowPkg tailReadPkg completionPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute, endpointRoute,
    _endpointPkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have ledgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary diagonalUnary endpointRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary tailWindowUnary tailRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed tailReadUnary diagonalUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
              hsame row tailWindow ∨ hsame row readback ∨ hsame row dyadicLedger ∨
                hsame row diagonalPacket ∨ hsame row completionRead ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont schedule selector window ∧
              Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
                Cont window tailWindow tailRead ∧ Cont tailRead diagonalPacket completionRead ∧
                  PkgSig bundle tailWindow pkg ∧ PkgSig bundle tailRead pkg ∧
                    PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
                      (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, ledgerRoute, endpointRoute, tailRoute, completionRoute,
          tailWindowPkg, tailReadPkg, completionPkg⟩
  }
  exact ⟨cert, tailReadUnary, completionUnary⟩

end BEDC.Derived.StreamDiagonalSelectorUp

import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_divergence_oracle_exclusion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name refusal readback
      sealed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont terminal normal refusal ->
        Cont refusal continuation readback ->
          Cont provenance name sealed ->
            PkgSig bundle readback pkg ->
              PkgSig bundle sealed pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminal ∨ hsame row normal ∨ hsame row refusal ∨
                        hsame row readback)
                    (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                    hsame ∧
                  UnaryHistory refusal ∧ UnaryHistory readback ∧ UnaryHistory sealed ∧
                    Cont terminal normal refusal ∧ Cont refusal continuation readback ∧
                      Cont provenance name sealed ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle readback pkg ∧ PkgSig bundle sealed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalRefusal refusalContinuationReadback provenanceNameSealed
    readbackPkg sealedPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRefusal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed refusalUnary continuationUnary refusalContinuationReadback
  have sealedUnary : UnaryHistory sealed :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameSealed
  have readbackSource :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row normal ∨ hsame row refusal ∨
              hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro readback readbackSource
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, readbackPkg⟩
    }
  exact
    ⟨cert, refusalUnary, readbackUnary, sealedUnary, terminalNormalRefusal,
      refusalContinuationReadback, provenanceNameSealed, provenancePkg, readbackPkg,
      sealedPkg⟩

end BEDC.Derived.ZnormalUp

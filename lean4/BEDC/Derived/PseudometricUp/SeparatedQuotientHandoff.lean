import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_separated_quotient_handoff [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      distanceRead boundaryRead quotientRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont distance stream distanceRead ->
        Cont zeroRow transport boundaryRead ->
          Cont boundaryRead replay quotientRead ->
            PkgSig bundle quotientRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row quotientRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row point ∨ hsame row distance ∨ hsame row zeroRow ∨
                      hsame row boundaryRead ∨ hsame row quotientRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle quotientRead pkg)
                  hsame ∧
                UnaryHistory distanceRead ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory quotientRead ∧ Cont stream readback dyadic ∧
                    Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle Pkg PkgSig hsame
  intro carrier distanceStreamRead zeroTransportBoundary boundaryReplayQuotient quotientPkg
  obtain ⟨_pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed distanceUnary streamUnary distanceStreamRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportBoundary
  have quotientReadUnary : UnaryHistory quotientRead :=
    unary_cont_closed boundaryReadUnary replayUnary boundaryReplayQuotient
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row quotientRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row zeroRow ∨
              hsame row boundaryRead ∨ hsame row quotientRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle quotientRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro quotientRead ⟨hsame_refl quotientRead, quotientReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, quotientPkg⟩
  }
  exact
    ⟨cert, distanceReadUnary, boundaryReadUnary, quotientReadUnary,
      streamReadbackDyadic, dyadicSealZero⟩

end BEDC.Derived.PseudometricUp

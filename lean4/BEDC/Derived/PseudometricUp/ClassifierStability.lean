import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_classifier_stability [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName pointRead
      zeroBoundaryRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      hsame pointRead point ->
        Cont zeroRow transport zeroBoundaryRead ->
          Cont pointRead zeroBoundaryRead classifierRead ->
            PkgSig bundle zeroBoundaryRead pkg ->
              PkgSig bundle classifierRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row point ∨ hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨
                        hsame row classifierRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle classifierRead pkg)
                    hsame ∧
                  UnaryHistory pointRead ∧ UnaryHistory zeroBoundaryRead ∧
                    UnaryHistory classifierRead ∧ Cont stream readback dyadic ∧
                      Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle Pkg PkgSig hsame
  intro carrier pointSame zeroBoundaryRoute classifierRoute _zeroBoundaryPkg classifierPkg
  obtain ⟨pointUnary, _distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have pointReadUnary : UnaryHistory pointRead :=
    unary_transport pointUnary (hsame_symm pointSame)
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroBoundaryRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed pointReadUnary zeroBoundaryUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨
              hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro classifierRead ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, classifierPkg⟩
  }
  exact
    ⟨cert, pointReadUnary, zeroBoundaryUnary, classifierUnary, streamReadbackDyadic,
      dyadicSealZero⟩

end BEDC.Derived.PseudometricUp

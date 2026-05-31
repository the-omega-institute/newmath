import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_kernel_source_carrier [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      sourceRead reflectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont point distance sourceRead ->
        Cont zeroRow transport reflectedRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle reflectedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row point ∨ hsame row distance ∨ hsame row sourceRead ∨
                      hsame row zeroRow ∨ hsame row reflectedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle sourceRead pkg ∧ PkgSig bundle reflectedRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory reflectedRead ∧
                  Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert
  intro carrier sourceRoute reflectedRoute sourcePkg reflectedPkg
  obtain ⟨pointUnary, distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed pointUnary distanceUnary sourceRoute
  have reflectedUnary : UnaryHistory reflectedRead :=
    unary_cont_closed zeroUnary transportUnary reflectedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row sourceRead ∨
              hsame row zeroRow ∨ hsame row reflectedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle sourceRead pkg ∧
              PkgSig bundle reflectedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, sourcePkg, reflectedPkg⟩
  }
  exact ⟨cert, sourceUnary, reflectedUnary, streamReadbackDyadic, dyadicSealZero⟩

end BEDC.Derived.PseudometricUp

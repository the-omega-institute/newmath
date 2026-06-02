import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_kernel_route [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg →
      Cont point distance kernelRead →
        PkgSig bundle kernelRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row point ∨ hsame row distance ∨ hsame row kernelRead ∨
                  hsame row zeroRow ∨ hsame row localName)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle kernelRead pkg)
              hsame ∧
            UnaryHistory kernelRead ∧ Cont stream readback dyadic ∧
              Cont dyadic sealRow zeroRow ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert
  intro carrier pointDistanceKernel kernelPkg
  obtain ⟨pointUnary, distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed pointUnary distanceUnary pointDistanceKernel
  have kernelSource :
      (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row) kernelRead := by
    exact ⟨hsame_refl kernelRead, kernelUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row kernelRead ∨
              hsame row zeroRow ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle kernelRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro kernelRead kernelSource
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
      exact ⟨source.right, localNamePkg, kernelPkg⟩
  }
  exact ⟨cert, kernelUnary, streamReadbackDyadic, dyadicSealZero, localNamePkg⟩

end BEDC.Derived.PseudometricUp

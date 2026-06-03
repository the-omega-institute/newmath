import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_located_metric_source_exhaustion [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName locatedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont distance dyadic locatedRead ->
        PkgSig bundle locatedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row distance ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row readback ∨ hsame row sealRow ∨ hsame row zeroRow ∨
                    hsame row locatedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle locatedRead pkg)
              hsame ∧
            UnaryHistory locatedRead ∧ Cont stream readback dyadic ∧
              Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier locatedRoute locatedPkg
  obtain ⟨_pointUnary, distanceUnary, dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed distanceUnary dyadicUnary locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row zeroRow ∨
                hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle locatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, locatedPkg⟩
  }
  exact ⟨cert, locatedUnary, streamReadbackDyadic, dyadicSealZero⟩

end BEDC.Derived.PseudometricUp

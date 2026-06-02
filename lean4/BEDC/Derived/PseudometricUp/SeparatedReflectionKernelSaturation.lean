import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_separated_reflection_kernel_saturation [AskSetup]
    [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      distanceRead zeroRead reflectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg ->
      Cont distance stream distanceRead ->
        Cont zeroRow transport zeroRead ->
          Cont zeroRead sealRow reflectedRead ->
            PkgSig bundle reflectedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row reflectedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row distance ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row readback ∨ hsame row sealRow ∨ hsame row zeroRow ∨
                        hsame row reflectedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle reflectedRead pkg)
                  hsame ∧
                UnaryHistory distanceRead ∧ UnaryHistory zeroRead ∧
                  UnaryHistory reflectedRead := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier distanceStreamRead zeroTransportRead zeroSealReflected reflectedPkg
  obtain ⟨_pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary, sealUnary,
    zeroUnary, transportUnary, _replayUnary, _localNameUnary, _streamReadbackDyadic,
    _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed distanceUnary streamUnary distanceStreamRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportRead
  have reflectedReadUnary : UnaryHistory reflectedRead :=
    unary_cont_closed zeroReadUnary sealUnary zeroSealReflected
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reflectedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row zeroRow ∨
                hsame row reflectedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle reflectedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro reflectedRead ⟨hsame_refl reflectedRead, reflectedReadUnary⟩
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
      exact ⟨source.right, localNamePkg, reflectedPkg⟩
  }
  exact ⟨cert, distanceReadUnary, zeroReadUnary, reflectedReadUnary⟩

end BEDC.Derived.PseudometricUp

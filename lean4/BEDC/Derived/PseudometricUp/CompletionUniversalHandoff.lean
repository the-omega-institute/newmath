import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCompletionUniversalHandoff [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      distanceRead sealedDistance zeroBoundaryRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont distance stream distanceRead ->
        Cont distanceRead sealRow sealedDistance ->
          Cont zeroRow transport zeroBoundaryRead ->
            Cont sealedDistance zeroBoundaryRead completionRead ->
              PkgSig bundle completionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row point ∨ hsame row distance ∨ hsame row distanceRead ∨
                        hsame row sealedDistance ∨ hsame row zeroRow ∨
                          hsame row zeroBoundaryRead ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle completionRead pkg)
                    hsame ∧ UnaryHistory distanceRead ∧ UnaryHistory sealedDistance ∧
                  UnaryHistory zeroBoundaryRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier distanceRoute sealedRoute zeroBoundaryRoute completionRoute completionPkg
  obtain ⟨_pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    sealUnary, zeroUnary, transportUnary, _replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed distanceUnary streamUnary distanceRoute
  have sealedDistanceUnary : UnaryHistory sealedDistance :=
    unary_cont_closed distanceReadUnary sealUnary sealedRoute
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroBoundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealedDistanceUnary zeroBoundaryUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row distanceRead ∨
              hsame row sealedDistance ∨ hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, completionPkg⟩
  }
  exact
    ⟨cert, distanceReadUnary, sealedDistanceUnary, zeroBoundaryUnary, completionUnary⟩

end BEDC.Derived.PseudometricUp

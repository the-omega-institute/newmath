import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCarrier_modulus_ledger_exactness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho modulusRead ->
          Cont modulusRead M boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                      hsame row M ∨ hsame row modulusRead ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K F radiusRead ∧
                      Cont radiusRead rho modulusRead ∧ Cont modulusRead M boundaryRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory radiusRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM radiusModulus modulusBoundary boundaryPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, radiusRoute, _handoffRoute, pkgP, _pkgN⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed radiusUnary unaryRho radiusModulus
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed modulusUnary unaryM modulusBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
              hsame row M ∨ hsame row modulusRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho modulusRead ∧
              Cont modulusRead M boundaryRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        ⟨source.right, radiusRoute, radiusModulus, modulusBoundary, pkgP, boundaryPkg⟩
  }
  exact ⟨cert, radiusUnary, modulusUnary, boundaryUnary⟩

end BEDC.Derived.EquicontinuityUp

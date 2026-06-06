import BEDC.Derived.EquicontinuityUp.FiniteModulusCarrier

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityContinuousMapModulusRoute [AskSetup] [PackageSetup]
    {K F eps rho M G T R P N compactRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFiniteModulusCarrier K F eps rho M G T R P N bundle pkg ->
      Cont K F compactRead ->
        Cont compactRead rho modulusRead ->
          PkgSig bundle modulusRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                    hsame row M ∨ hsame row G ∨ hsame row compactRead ∨
                      hsame row modulusRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F compactRead ∧
                    Cont compactRead rho modulusRead ∧ PkgSig bundle modulusRead pkg)
                hsame ∧ UnaryHistory compactRead ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: EquicontinuityFiniteModulusCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier compactRoute modulusRoute modulusPkg
  obtain ⟨unaryK, unaryF, _unaryEps, unaryRho, _unaryM, _unaryG, _unaryT,
    _unaryR, _unaryP, _unaryN, _epsRoute, _modulusHandoff, _boundaryRoute,
    _pkgP, _pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed compactUnary unaryRho modulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row G ∨ hsame row compactRead ∨ hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F compactRead ∧
              Cont compactRead rho modulusRead ∧ PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro modulusRead ⟨hsame_refl modulusRead, modulusUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, modulusRoute, modulusPkg⟩
  }
  exact ⟨cert, compactUnary, modulusUnary⟩

end BEDC.Derived.EquicontinuityUp

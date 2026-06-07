import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootObligationUniformModulus [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead uniformRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      UnaryHistory M →
        Cont radiusRead rho uniformRead →
          Cont uniformRead M handoffRead →
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                    hsame row P ∨ hsame row N ∨ hsame row uniformRead ∨
                      hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F radiusRead ∧
                    Cont radiusRead rho uniformRead ∧ Cont uniformRead M handoffRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧ UnaryHistory uniformRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM radiusUniform uniformHandoff
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, compactFamily, _radiusHandoff,
    pkgP, pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed radiusUnary unaryRho radiusUniform
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed uniformUnary unaryM uniformHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨ hsame row P ∨
              hsame row N ∨ hsame row uniformRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho uniformRead ∧
              Cont uniformRead M handoffRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact ⟨source.right, compactFamily, radiusUniform, uniformHandoff, pkgP, pkgN⟩
  }
  exact ⟨cert, uniformUnary, handoffUnary⟩

end BEDC.Derived.EquicontinuityUp

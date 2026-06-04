import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootCompactSourceLock [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactRead lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont K F compactRead ->
        Cont compactRead R lockedRead ->
          PkgSig bundle lockedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row P ∨
                    hsame row N ∨ hsame row compactRead ∨ hsame row lockedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F compactRead ∧
                    Cont compactRead R lockedRead ∧ PkgSig bundle lockedRead pkg ∧
                      PkgSig bundle P pkg)
                hsame ∧ UnaryHistory compactRead ∧ UnaryHistory lockedRead ∧
              Cont K F compactRead ∧ Cont compactRead R lockedRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute lockedRoute lockedPkg
  obtain ⟨unaryK, unaryF, _unaryRho, unaryR, _unaryN, _radiusRoute, _handoffRoute,
    pkgP, _pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed compactUnary unaryR lockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
              hsame row compactRead ∨ hsame row lockedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F compactRead ∧ Cont compactRead R lockedRead ∧
              PkgSig bundle lockedRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lockedRead ⟨hsame_refl lockedRead, lockedUnary⟩
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
      exact ⟨source.right, compactRoute, lockedRoute, lockedPkg, pkgP⟩
  }
  exact ⟨cert, compactUnary, lockedUnary, compactRoute, lockedRoute⟩

end BEDC.Derived.EquicontinuityUp

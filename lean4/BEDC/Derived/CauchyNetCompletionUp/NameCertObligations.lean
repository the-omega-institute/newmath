import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row H ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ Cont D W Q ∨
                  Cont Q M U ∨ Cont U S R ∨ Cont R A H)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row H)
          hsame ∧
        hsame H (append R A) ∧ UnaryHistory H := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory append
  intro carrier
  obtain ⟨_unaryD, _unaryW, _unaryQ, _unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    unaryH, _unaryC, _unaryP, _unaryN, _boundaryRoute, _mooreRoute, _uniformRoute,
      sealRoute, provenancePkg, localNamePkg⟩ := carrier
  have sealExact : hsame H (append R A) := by
    cases sealRoute
    exact hsame_refl _
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row H ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ Cont D W Q ∨
                  Cont Q M U ∨ Cont U S R ∨ Cont R A H)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row H)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro H ⟨hsame_refl H, unaryH⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact ⟨cert, sealExact, unaryH⟩

end BEDC.Derived.CauchyNetCompletionUp

import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionUniformHandoffNonescape [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead U uniformRead ->
          SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row U ∨
                  hsame row uniformRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W boundaryRead ∧
                  Cont boundaryRead U uniformRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory boundaryRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute uniformRoute
  obtain ⟨unaryD, unaryW, _unaryQ, _unaryM, unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed boundaryUnary unaryU uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row U ∨
              hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧
              Cont boundaryRead U uniformRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, uniformRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, uniformUnary⟩

end BEDC.Derived.CauchyNetCompletionUp

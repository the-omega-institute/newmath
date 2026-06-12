import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionDirectedWindowTerminality [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead requestRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead Q requestRead ->
          Cont requestRead U handoffRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                        hsame row U ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                          hsame row boundaryRead ∨ hsame row requestRead ∨
                            hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D W boundaryRead ∧
                        Cont boundaryRead Q requestRead ∧ Cont requestRead U handoffRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory requestRead ∧
                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier boundaryRoute requestRoute handoffRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, unaryQ, _unaryM, unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed boundaryUnary unaryQ requestRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed requestUnary unaryU handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row boundaryRead ∨
                hsame row requestRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧ Cont boundaryRead Q requestRead ∧
              Cont requestRead U handoffRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, requestRoute, handoffRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, requestUnary, handoffUnary⟩

end BEDC.Derived.CauchyNetCompletionUp

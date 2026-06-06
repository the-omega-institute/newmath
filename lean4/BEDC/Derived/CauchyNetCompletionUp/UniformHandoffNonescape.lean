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
    {D W Q M U S R A H C P N boundaryRead requestRead uniformRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead Q requestRead ->
          Cont requestRead U uniformRead ->
            Cont uniformRead A sealRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row U ∨
                          hsame row A ∨ hsame row boundaryRead ∨ hsame row requestRead ∨
                            hsame row uniformRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D W boundaryRead ∧
                          Cont boundaryRead Q requestRead ∧ Cont requestRead U uniformRead ∧
                            Cont uniformRead A sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory requestRead ∧
                      UnaryHistory uniformRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier boundaryRoute requestRoute uniformRoute sealRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, unaryQ, _unaryM, unaryU, _unaryS, _unaryR, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed boundaryUnary unaryQ requestRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed requestUnary unaryU uniformRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed uniformUnary unaryA sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row U ∨ hsame row A ∨
              hsame row boundaryRead ∨ hsame row requestRead ∨ hsame row uniformRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧ Cont boundaryRead Q requestRead ∧
              Cont requestRead U uniformRead ∧ Cont uniformRead A sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, requestRoute, uniformRoute, sealRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, requestUnary, uniformUnary, sealUnary⟩

end BEDC.Derived.CauchyNetCompletionUp

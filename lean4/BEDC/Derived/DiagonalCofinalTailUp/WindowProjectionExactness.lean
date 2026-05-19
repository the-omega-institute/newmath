import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_window_projection_exactness [AskSetup] [PackageSetup]
    {q s g d r w h c p n windowRead projection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont c r windowRead ->
        Cont windowRead p projection ->
          PkgSig bundle projection pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row projection /\ UnaryHistory row)
                (fun row : BHist => Cont windowRead p row /\ PkgSig bundle projection pkg)
                (fun row : BHist => hsame row projection /\ PkgSig bundle projection pkg)
                hsame /\
              UnaryHistory c /\ UnaryHistory r /\ UnaryHistory windowRead /\
                UnaryHistory projection /\ Cont c r windowRead /\
                  Cont windowRead p projection /\ PkgSig bundle p pkg /\
                    PkgSig bundle projection pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier windowRoute projectionRoute projectionPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, _wUnary, _hUnary, cUnary,
    pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cUnary rUnary windowRoute
  have projectionUnary : UnaryHistory projection :=
    unary_cont_closed windowUnary pUnary projectionRoute
  have sourceAtProjection :
      (fun row : BHist => hsame row projection /\ UnaryHistory row) projection := by
    exact ⟨hsame_refl projection, projectionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row projection /\ UnaryHistory row)
          (fun row : BHist => Cont windowRead p row /\ PkgSig bundle projection pkg)
          (fun row : BHist => hsame row projection /\ PkgSig bundle projection pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro projection sourceAtProjection
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
      exact
        ⟨cont_result_hsame_transport projectionRoute (hsame_symm source.left),
          projectionPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, projectionPkg⟩
  }
  exact
    ⟨cert, cUnary, rUnary, windowUnary, projectionUnary, windowRoute, projectionRoute,
      pPkg, projectionPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp

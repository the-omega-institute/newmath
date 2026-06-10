import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailPublicConsumerExactness [AskSetup] [PackageSetup]
    {Q S G D R W H C P N seedWindow tailRead dyadicRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier Q S G D R W H C P N bundle pkg →
      Cont Q S seedWindow →
        Cont S G tailRead →
          Cont G D dyadicRead →
            Cont D R sealRead →
              Cont sealRead N namedRead →
                hsame H C →
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Q ∨ hsame row S ∨ hsame row G ∨ hsame row D ∨
                        hsame row R ∨ hsame row W ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Q S seedWindow ∧ Cont S G tailRead ∧
                        Cont G D dyadicRead ∧ Cont D R sealRead ∧
                          Cont sealRead N namedRead ∧ hsame H C)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier seedRoute tailRoute dyadicRoute sealRoute namedRoute transportLock
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _qsRoute, _gdRoute, _whRoute, _pPkg⟩ := carrier
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed qUnary sUnary seedRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary gUnary tailRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed gUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dUnary rUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, seedRoute, tailRoute, dyadicRoute, sealRoute, namedRoute,
          transportLock⟩
  }

end BEDC.Derived.DiagonalCofinalTailUp

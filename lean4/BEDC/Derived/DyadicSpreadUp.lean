import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicSpreadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicSpreadCarrier [AskSetup] [PackageSetup]
    (P W I S R A K C H Q L N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory P ∧ UnaryHistory W ∧ UnaryHistory I ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory K ∧ UnaryHistory C ∧
      UnaryHistory H ∧ UnaryHistory Q ∧ UnaryHistory L ∧ UnaryHistory N ∧
        PkgSig bundle L pkg ∧ PkgSig bundle N pkg

theorem DyadicSpreadWindowStability [AskSetup] [PackageSetup]
    {P W I S R A K C H Q L N prefixRead dyadicRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSpreadCarrier P W I S R A K C H Q L N bundle pkg ->
      Cont P W prefixRead ->
        Cont prefixRead I dyadicRead ->
          Cont dyadicRead R regularRead ->
            hsame H (append P W) ->
              PkgSig bundle regularRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row W ∨ hsame row I ∨ hsame row S ∨
                        hsame row R ∨ hsame row regularRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont P W prefixRead ∧
                        Cont prefixRead I dyadicRead ∧
                          Cont dyadicRead R regularRead ∧
                            PkgSig bundle regularRead pkg)
                    hsame ∧
                  UnaryHistory prefixRead ∧ UnaryHistory dyadicRead ∧
                    UnaryHistory regularRead ∧ hsame H (append P W) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame append SemanticNameCert UnaryHistory
  intro carrier prefixRoute dyadicRoute regularRoute supportSame regularPkg
  obtain ⟨pUnary, wUnary, iUnary, _sUnary, rUnary, _aUnary, _kUnary, _cUnary,
    _hUnary, _qUnary, _lUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed pUnary wUnary prefixRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed prefixUnary iUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row W ∨ hsame row I ∨ hsame row S ∨ hsame row R ∨
              hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P W prefixRead ∧ Cont prefixRead I dyadicRead ∧
              Cont dyadicRead R regularRead ∧ PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead ⟨hsame_refl regularRead, regularUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, dyadicRoute, regularRoute, regularPkg⟩
  }
  exact ⟨cert, prefixUnary, dyadicUnary, regularUnary, supportSame⟩

end BEDC.Derived.DyadicSpreadUp

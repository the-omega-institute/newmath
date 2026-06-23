import BEDC.Derived.IntervalNewtonUp

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntervalNewtonRealReadbackScope [AskSetup] [PackageSetup]
    {B F D N K V R H C P L boxRead correctionRead validatedRead realRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory F ->
        UnaryHistory D ->
          UnaryHistory N ->
            UnaryHistory K ->
              UnaryHistory V ->
                UnaryHistory R ->
                  UnaryHistory H ->
                    Cont B F boxRead ->
                      Cont D N correctionRead ->
                        Cont K V validatedRead ->
                          Cont validatedRead R realRead ->
                            Cont H realRead named ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle L pkg ->
                                  PkgSig bundle named pkg ->
                                    SemanticNameCert
                                        (fun row : BHist => hsame row named ∧
                                          UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row B ∨ hsame row F ∨ hsame row D ∨
                                            hsame row N ∨ hsame row K ∨ hsame row V ∨
                                              hsame row R ∨ hsame row H ∨
                                                hsame row named)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont B F boxRead ∧
                                            Cont D N correctionRead ∧
                                              Cont K V validatedRead ∧
                                                Cont validatedRead R realRead ∧
                                                  Cont H realRead named ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle L pkg ∧
                                                        PkgSig bundle named pkg)
                                        hsame ∧
                                      UnaryHistory boxRead ∧
                                        UnaryHistory correctionRead ∧
                                          UnaryHistory validatedRead ∧
                                            UnaryHistory realRead ∧
                                              UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro bUnary fUnary dUnary nUnary kUnary vUnary rUnary hUnary boxRoute
    correctionRoute validatedRoute realRoute namedRoute pkgP pkgL namedPkg
  have boxUnary : UnaryHistory boxRead :=
    unary_cont_closed bUnary fUnary boxRoute
  have correctionUnary : UnaryHistory correctionRead :=
    unary_cont_closed dUnary nUnary correctionRoute
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed kUnary vUnary validatedRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed validatedUnary rUnary realRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary realUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row F ∨ hsame row D ∨ hsame row N ∨ hsame row K ∨
              hsame row V ∨ hsame row R ∨ hsame row H ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B F boxRead ∧ Cont D N correctionRead ∧
              Cont K V validatedRead ∧ Cont validatedRead R realRead ∧
                Cont H realRead named ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg ∧
                  PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boxRoute, correctionRoute, validatedRoute, realRoute,
          namedRoute, pkgP, pkgL, namedPkg⟩
  }
  exact ⟨cert, boxUnary, correctionUnary, validatedUnary, realUnary, namedUnary⟩

end BEDC.Derived.IntervalNewtonUp

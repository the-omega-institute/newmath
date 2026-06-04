import BEDC.Derived.LowerRealUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerRealPublicLocatedSupremumHandoff [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerRead rationalRead realRead namedRead supremumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                UnaryHistory P ->
                  Cont L0 W lowerRead ->
                    Cont lowerRead R rationalRead ->
                      Cont rationalRead E realRead ->
                        Cont realRead N namedRead ->
                          Cont namedRead P supremumRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle supremumRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row supremumRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row L0 ∨ hsame row W ∨ hsame row R ∨
                                        hsame row E ∨ hsame row N ∨ hsame row P ∨
                                          hsame row supremumRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont L0 W lowerRead ∧
                                        Cont lowerRead R rationalRead ∧
                                          Cont rationalRead E realRead ∧
                                            Cont realRead N namedRead ∧
                                              Cont namedRead P supremumRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle supremumRead pkg)
                                    hsame ∧
                                  UnaryHistory lowerRead ∧ UnaryHistory rationalRead ∧
                                    UnaryHistory realRead ∧ UnaryHistory namedRead ∧
                                      UnaryHistory supremumRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldRows l0Unary wUnary rUnary eUnary nUnary pUnary lowerRoute rationalRoute
    realRoute namedRoute supremumRoute pPkg supremumPkg
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed l0Unary wUnary lowerRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed namedUnary pUnary supremumRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supremumRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row N ∨
              hsame row P ∨ hsame row supremumRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L0 W lowerRead ∧ Cont lowerRead R rationalRead ∧
              Cont rationalRead E realRead ∧ Cont realRead N namedRead ∧
                Cont namedRead P supremumRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle supremumRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supremumRead ⟨hsame_refl supremumRead, supremumUnary⟩
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
        ⟨source.right, lowerRoute, rationalRoute, realRoute, namedRoute, supremumRoute,
          pPkg, supremumPkg⟩
  }
  exact ⟨cert, lowerUnary, rationalUnary, realUnary, namedUnary, supremumUnary⟩

end BEDC.Derived.LowerRealUp

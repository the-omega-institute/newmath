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

theorem LowerRealPublicRegSeqRatRealRoute [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerRead rationalRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] →
      UnaryHistory L0 →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory N →
                Cont L0 W lowerRead →
                  Cont lowerRead R rationalRead →
                    Cont rationalRead E realRead →
                      Cont realRead N namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle namedRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row L0 ∨ hsame row W ∨ hsame row R ∨
                                    hsame row E ∨ hsame row N ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont L0 W lowerRead ∧
                                    Cont lowerRead R rationalRead ∧
                                      Cont rationalRead E realRead ∧
                                        Cont realRead N namedRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle namedRead pkg)
                                hsame ∧
                              UnaryHistory lowerRead ∧ UnaryHistory rationalRead ∧
                                UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldRows l0Unary wUnary rUnary eUnary nUnary lowerRoute rationalRoute realRoute
    namedRoute pPkg namedPkg
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed l0Unary wUnary lowerRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L0 W lowerRead ∧ Cont lowerRead R rationalRead ∧
              Cont rationalRead E realRead ∧ Cont realRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, rationalRoute, realRoute, namedRoute, pPkg, namedPkg⟩
  }
  exact ⟨cert, lowerUnary, rationalUnary, realUnary, namedUnary⟩

end BEDC.Derived.LowerRealUp

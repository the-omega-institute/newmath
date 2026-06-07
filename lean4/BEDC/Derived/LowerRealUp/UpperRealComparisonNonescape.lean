import BEDC.Derived.LowerRealUp.PublicPackageScope

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerRealUpperRealComparisonNonescape [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerRead rationalRead realRead namedRead boundaryRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LowerRealPublicPackage L0 W R E H C P N bundle pkg →
      Cont L0 W lowerRead →
        Cont lowerRead R rationalRead →
          Cont rationalRead E realRead →
            Cont realRead N namedRead →
              Cont namedRead E sealRead →
                Cont sealRead N boundaryRead →
                  PkgSig bundle boundaryRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L0 ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                            hsame row N ∨ hsame row sealRead ∨ hsame row boundaryRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont L0 W lowerRead ∧
                            Cont lowerRead R rationalRead ∧ Cont rationalRead E realRead ∧
                              Cont realRead N namedRead ∧ Cont namedRead E sealRead ∧
                                Cont sealRead N boundaryRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle boundaryRead pkg)
                        hsame ∧
                      UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro package lowerRoute rationalRoute realRoute namedRoute sealRoute boundaryRoute
    boundaryPkg
  obtain ⟨fieldRows, l0Unary, wUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, pPkg, _nPkg⟩ := package
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed l0Unary wUnary lowerRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed namedUnary eUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary nUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row N ∨
              hsame row sealRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L0 W lowerRead ∧ Cont lowerRead R rationalRead ∧
              Cont rationalRead E realRead ∧ Cont realRead N namedRead ∧
                Cont namedRead E sealRead ∧ Cont sealRead N boundaryRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, rationalRoute, realRoute, namedRoute, sealRoute,
          boundaryRoute, pPkg, boundaryPkg⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.LowerRealUp

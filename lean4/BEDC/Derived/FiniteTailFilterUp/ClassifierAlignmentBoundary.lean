import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterClassifierAlignmentBoundary [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          Cont realWindowRead C classifierRead ->
            PkgSig bundle classifierRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row B ∨
                        hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row classifierRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S D R ∧ Cont R B Q ∧
                        Cont Q E sealRead ∧ Cont sealRead H realWindowRead ∧
                          Cont realWindowRead C classifierRead ∧ PkgSig bundle classifierRead pkg)
                    hsame ∧
                UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: FiniteTailFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute realWindowRoute classifierRoute classifierPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, unaryC, routeR, routeQ,
    _sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryRealWindow unaryC classifierRoute
  have sourceClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row B ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRead ∧
              Cont sealRead H realWindowRead ∧ Cont realWindowRead C classifierRead ∧
                PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceClassifier
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeR, routeQ, sealRoute, realWindowRoute, classifierRoute,
          classifierPkg⟩
  }
  exact ⟨cert, classifierUnary⟩

end BEDC.Derived.FiniteTailFilterUp

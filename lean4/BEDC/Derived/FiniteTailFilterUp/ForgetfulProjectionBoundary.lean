import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterForgetfulProjectionBoundary [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead projectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          Cont realWindowRead C projectionRead ->
            PkgSig bundle projectionRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row projectionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row B ∨
                        hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row projectionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S D R ∧ Cont R B Q ∧
                        Cont Q E sealRead ∧ Cont sealRead H realWindowRead ∧
                          Cont realWindowRead C projectionRead ∧
                            PkgSig bundle projectionRead pkg)
                    hsame ∧
                UnaryHistory projectionRead := by
  -- BEDC touchpoint anchor: FiniteTailFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute realWindowRoute projectionRoute projectionPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, unaryC, routeR, routeQ,
    _sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have realWindowUnary : UnaryHistory realWindowRead :=
    unary_cont_closed sealUnary unaryH realWindowRoute
  have projectionUnary : UnaryHistory projectionRead :=
    unary_cont_closed realWindowUnary unaryC projectionRoute
  have sourceProjection :
      (fun row : BHist => hsame row projectionRead ∧ UnaryHistory row) projectionRead := by
    exact ⟨hsame_refl projectionRead, projectionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row projectionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row B ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row projectionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRead ∧
              Cont sealRead H realWindowRead ∧ Cont realWindowRead C projectionRead ∧
                PkgSig bundle projectionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro projectionRead sourceProjection
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
        ⟨source.right, routeR, routeQ, sealRoute, realWindowRoute, projectionRoute,
          projectionPkg⟩
  }
  exact ⟨cert, projectionUnary⟩

end BEDC.Derived.FiniteTailFilterUp

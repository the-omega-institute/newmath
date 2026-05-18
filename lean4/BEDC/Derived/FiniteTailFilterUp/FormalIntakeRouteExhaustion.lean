import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_formal_intake_route_exhaustion
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead classifierRead intakeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont Q E sealRead →
        Cont sealRead H realWindowRead →
          Cont realWindowRead C classifierRead →
            Cont classifierRead N intakeRead →
              PkgSig bundle intakeRead pkg →
                UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                  UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                    UnaryHistory sealRead ∧ UnaryHistory realWindowRead ∧
                      UnaryHistory classifierRead ∧ UnaryHistory intakeRead ∧
                        Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRead ∧
                          Cont sealRead H realWindowRead ∧
                            Cont realWindowRead C classifierRead ∧
                              Cont classifierRead N intakeRead ∧ hsame N E ∧
                                PkgSig bundle intakeRead pkg ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row intakeRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist => hsame row intakeRead ∧
                                      Cont sealRead H realWindowRead ∧
                                        Cont realWindowRead C classifierRead ∧
                                          Cont classifierRead N intakeRead)
                                    (fun row : BHist => hsame row intakeRead ∧
                                      PkgSig bundle intakeRead pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sealRoute realWindowRoute classifierRoute intakeRoute intakePkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, unaryC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryClassifier : UnaryHistory classifierRead :=
    unary_cont_closed unaryRealWindow unaryC classifierRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryIntake : UnaryHistory intakeRead :=
    unary_cont_closed unaryClassifier unaryN intakeRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row intakeRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row intakeRead ∧ Cont sealRead H realWindowRead ∧
          Cont realWindowRead C classifierRead ∧ Cont classifierRead N intakeRead)
        (fun row : BHist => hsame row intakeRead ∧ PkgSig bundle intakeRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro intakeRead ⟨hsame_refl intakeRead, unaryIntake⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, realWindowRoute, classifierRoute, intakeRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, intakePkg⟩
    }
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryClassifier, unaryIntake, routeR, routeQ, sealRoute,
      realWindowRoute, classifierRoute, intakeRoute, sameNameSeal, intakePkg, cert⟩

end BEDC.Derived.FiniteTailFilterUp

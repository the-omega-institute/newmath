import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterExactBoundaryTerminalNormalForm
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead exactBoundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          UnaryHistory C ->
            Cont realWindowRead C exactBoundary ->
              Cont exactBoundary N terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                      UnaryHistory sealRead ∧ UnaryHistory realWindowRead ∧
                        UnaryHistory exactBoundary ∧ UnaryHistory terminal ∧
                          Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRead ∧
                            Cont sealRead H realWindowRead ∧
                              Cont realWindowRead C exactBoundary ∧
                                Cont exactBoundary N terminal ∧ hsame N E ∧
                                  PkgSig bundle terminal pkg ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row terminal ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row terminal ∧ Cont exactBoundary N terminal)
                                      (fun row : BHist =>
                                        hsame row terminal ∧ PkgSig bundle terminal pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sealRoute realWindowRoute unaryC exactBoundaryRoute terminalRoute terminalPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryCarrierC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryExactBoundary : UnaryHistory exactBoundary :=
    unary_cont_closed unaryRealWindow unaryC exactBoundaryRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryExactBoundary unaryN terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist => hsame row terminal ∧ Cont exactBoundary N terminal)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, unaryTerminal⟩
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, terminalRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, terminalPkg⟩
    }
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryExactBoundary, unaryTerminal, routeR, routeQ, sealRoute,
      realWindowRoute, exactBoundaryRoute, terminalRoute, sameNameSeal, terminalPkg,
      cert⟩

end BEDC.Derived.FiniteTailFilterUp

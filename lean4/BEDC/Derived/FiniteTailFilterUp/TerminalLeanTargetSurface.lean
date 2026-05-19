import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterTerminalLeanTargetSurface
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N windowRead regularRead tailRead sealRead terminal : BHist} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead B tailRead ->
            Cont tailRead E sealRead ->
              Cont sealRead N terminal ->
                UnaryHistory windowRead /\ UnaryHistory regularRead /\
                  UnaryHistory tailRead /\ UnaryHistory sealRead /\
                    UnaryHistory terminal /\ Cont S D windowRead /\
                      Cont windowRead R regularRead /\ Cont regularRead B tailRead /\
                        Cont tailRead E sealRead /\ Cont sealRead N terminal := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier windowRoute regularRoute tailRoute sealRoute terminalRoute
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, _unaryC, routeR, _routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryD windowRoute
  have unaryRegular : UnaryHistory regularRead :=
    unary_cont_closed unaryWindow unaryR regularRoute
  have unaryTail : UnaryHistory tailRead :=
    unary_cont_closed unaryRegular unaryB tailRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryTail unaryE sealRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unarySeal unaryN terminalRoute
  exact
    ⟨unaryWindow, unaryRegular, unaryTail, unarySeal, unaryTerminal, windowRoute,
      regularRoute, tailRoute, sealRoute, terminalRoute⟩

theorem FiniteTailFilterCarrier_lean_ready_obligation_surface
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realWindowRead uniformRead terminalRead
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H realWindowRead ->
          Cont realWindowRead C uniformRead ->
            Cont uniformRead H terminalRead ->
              Cont terminalRead N classifierRead ->
                UnaryHistory C ->
                  PkgSig bundle classifierRead pkg ->
                    UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                      UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                        UnaryHistory sealRow ∧ UnaryHistory realWindowRead ∧
                          UnaryHistory uniformRead ∧ UnaryHistory terminalRead ∧
                            UnaryHistory classifierRead ∧ Cont S D R ∧ Cont R B Q ∧
                              Cont Q E sealRow ∧ Cont sealRow H realWindowRead ∧
                                Cont realWindowRead C uniformRead ∧
                                  Cont uniformRead H terminalRead ∧
                                    Cont terminalRead N classifierRead ∧ hsame N E ∧
                                      PkgSig bundle classifierRead pkg ∧
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row classifierRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row classifierRead ∧
                                              Cont terminalRead N classifierRead)
                                          (fun row : BHist =>
                                            hsame row classifierRead ∧
                                              PkgSig bundle classifierRead pkg)
                                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sealRoute realWindowRoute uniformRoute terminalRoute classifierRoute
    unaryC classifierPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryCarrierC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryUniform : UnaryHistory uniformRead :=
    unary_cont_closed unaryRealWindow unaryC uniformRoute
  have unaryTerminal : UnaryHistory terminalRead :=
    unary_cont_closed unaryUniform unaryH terminalRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryClassifier : UnaryHistory classifierRead :=
    unary_cont_closed unaryTerminal unaryN classifierRoute
  have sourceAtClassifier :
      hsame classifierRead classifierRead ∧ UnaryHistory classifierRead :=
    ⟨hsame_refl classifierRead, unaryClassifier⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row classifierRead ∧ Cont terminalRead N classifierRead)
          (fun row : BHist =>
            hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceAtClassifier
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
      exact ⟨source.left, classifierRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, classifierPkg⟩
  }
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryUniform, unaryTerminal, unaryClassifier, routeR, routeQ,
      sealRoute, realWindowRoute, uniformRoute, terminalRoute, classifierRoute,
      sameNameSeal, classifierPkg, cert⟩

end BEDC.Derived.FiniteTailFilterUp

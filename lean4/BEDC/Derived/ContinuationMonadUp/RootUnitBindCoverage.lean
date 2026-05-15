import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_unit_bind_coverage [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont bindRead N terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory unitRead ∧ UnaryHistory bindRead ∧ UnaryHistory terminal ∧
                    Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                      Cont u f unitRead ∧ Cont K N bindRead ∧
                        Cont bindRead N terminal ∧ hsame N L ∧
                          PkgSig bundle terminal pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                Cont bindRead N row ∧ Cont u f unitRead ∧
                                  Cont K N bindRead)
                              (fun row : BHist =>
                                hsame row terminal ∧ PkgSig bundle terminal pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute terminalRoute terminalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryN bindRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryBindRead unaryN terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist => Cont bindRead N row ∧ Cont u f unitRead ∧ Cont K N bindRead)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro terminal (And.intro (hsame_refl terminal) unaryTerminal)
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨cont_result_hsame_transport terminalRoute (hsame_symm source.left),
            unitRoute, bindRoute⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left terminalPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryUnitRead,
      unaryBindRead, unaryTerminal, routeB, routeC, routeK, routeL, unitRoute,
      bindRoute, terminalRoute, sameEndpoint, terminalPkg, cert⟩

theorem ContinuationMonadCarrier_root_ledger_saturation_boundary [AskSetup] [PackageSetup]
    {A B C f g u H K L N ledgerRead saturatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N ledgerRead ->
        Cont ledgerRead N saturatedRead ->
          PkgSig bundle saturatedRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory N ∧ UnaryHistory ledgerRead ∧ UnaryHistory saturatedRead ∧
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont L N ledgerRead ∧ Cont ledgerRead N saturatedRead ∧
                      hsame N L ∧ PkgSig bundle saturatedRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row saturatedRead ∧ UnaryHistory row)
                          (fun row : BHist => Cont ledgerRead N row ∧ hsame N L)
                          (fun row : BHist =>
                            hsame row saturatedRead ∧ PkgSig bundle saturatedRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier ledgerRoute saturatedRoute saturatedPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryL unaryN ledgerRoute
  have unarySaturatedRead : UnaryHistory saturatedRead :=
    unary_cont_closed unaryLedgerRead unaryN saturatedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row saturatedRead ∧ UnaryHistory row)
        (fun row : BHist => Cont ledgerRead N row ∧ hsame N L)
        (fun row : BHist => hsame row saturatedRead ∧ PkgSig bundle saturatedRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro saturatedRead
            (And.intro (hsame_refl saturatedRead) unarySaturatedRead)
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨cont_result_hsame_transport saturatedRoute (hsame_symm source.left),
            sameEndpoint⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left saturatedPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryLedgerRead, unarySaturatedRead, routeB, routeC, routeK, routeL, ledgerRoute,
      saturatedRoute, sameEndpoint, saturatedPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp

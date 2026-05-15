import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_namecert_consumer_lock
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N audit formal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N audit ->
        Cont K N formal ->
          PkgSig bundle formal pkg ->
            SemanticNameCert
              (fun row : BHist =>
                ContinuationMonadCarrier A B C f g u H K L N ∧ Cont L N audit ∧
                  Cont K N formal ∧ hsame row formal)
              (fun row : BHist => hsame row formal ∧ Cont K N formal)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle formal pkg ∧ hsame N L)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier auditRoute formalRoute formalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have carrierPacket : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
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
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryK unaryN formalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro formal
          ⟨carrierPacket, auditRoute, formalRoute, hsame_refl formal⟩
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
          ⟨source.left, source.right.left, source.right.right.left,
            hsame_trans (hsame_symm same) source.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right.right.right, source.right.right.left⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm unaryFormal source.right.right.right, formalPkg,
          sameEndpoint⟩
  }

theorem ContinuationMonadCarrier_root_formal_handoff_saturation
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N audit ledger formal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N audit ->
        Cont audit N ledger ->
          Cont K N formal ->
            PkgSig bundle formal pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory audit ∧ UnaryHistory ledger ∧
                    UnaryHistory formal ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N audit ∧
                        Cont audit N ledger ∧ Cont K N formal ∧ hsame N L ∧
                          PkgSig bundle formal pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row formal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                Cont K N row ∧ Cont L N audit ∧ Cont audit N ledger)
                              (fun row : BHist =>
                                hsame row formal ∧ PkgSig bundle formal pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier auditRoute ledgerRoute formalRoute formalPkg
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
  have unaryAudit : UnaryHistory audit :=
    unary_cont_closed unaryL unaryN auditRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryAudit unaryN ledgerRoute
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryK unaryN formalRoute
  have sourceFormal :
      (fun row : BHist => hsame row formal ∧ UnaryHistory row) formal := by
    exact ⟨hsame_refl formal, unaryFormal⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row formal ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont K N row ∧ Cont L N audit ∧ Cont audit N ledger)
        (fun row : BHist => hsame row formal ∧ PkgSig bundle formal pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro formal sourceFormal
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
        exact
          ⟨cont_result_hsame_transport formalRoute (hsame_symm source.left),
            auditRoute, ledgerRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, formalPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryAudit, unaryLedger, unaryFormal, routeB, routeC, routeK, routeL,
      auditRoute, ledgerRoute, formalRoute, sameEndpoint, formalPkg, cert⟩

theorem ContinuationMonadCarrier_formal_route_target_exhaustion
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N namecert category readback target : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N namecert ->
        Cont namecert K category ->
          Cont category N readback ->
            Cont readback u target ->
              PkgSig bundle target pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory N ∧ UnaryHistory namecert ∧ UnaryHistory category ∧
                      UnaryHistory readback ∧ UnaryHistory target ∧ Cont A f B ∧
                        Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                          Cont L N namecert ∧ Cont namecert K category ∧
                            Cont category N readback ∧ Cont readback u target ∧
                              hsame N L ∧ PkgSig bundle target pkg ∧
                                SemanticNameCert
                                  (fun row : BHist => hsame row target ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    Cont readback u row ∧ Cont L N namecert ∧
                                      Cont namecert K category ∧ Cont category N readback)
                                  (fun row : BHist =>
                                    hsame row target ∧ PkgSig bundle target pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier namecertRoute categoryRoute readbackRoute targetRoute targetPkg
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
  have unaryNamecert : UnaryHistory namecert :=
    unary_cont_closed unaryL unaryN namecertRoute
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryNamecert unaryK categoryRoute
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryCategory unaryN readbackRoute
  have unaryTarget : UnaryHistory target :=
    unary_cont_closed unaryReadback unaryU targetRoute
  have sourceTarget :
      (fun row : BHist => hsame row target ∧ UnaryHistory row) target := by
    exact ⟨hsame_refl target, unaryTarget⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row target ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont readback u row ∧ Cont L N namecert ∧ Cont namecert K category ∧
            Cont category N readback)
        (fun row : BHist => hsame row target ∧ PkgSig bundle target pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro target sourceTarget
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
        exact
          ⟨cont_result_hsame_transport targetRoute (hsame_symm source.left),
            namecertRoute, categoryRoute, readbackRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, targetPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryNamecert, unaryCategory, unaryReadback, unaryTarget, routeB, routeC,
      routeK, routeL, namecertRoute, categoryRoute, readbackRoute, targetRoute,
      sameEndpoint, targetPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp

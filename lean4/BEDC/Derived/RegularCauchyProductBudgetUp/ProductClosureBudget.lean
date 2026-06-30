import BEDC.Derived.RegularCauchyProductBudgetUp.RealSealBoundary

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_product_closure_budget [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont A WA windowA ->
        Cont B WB windowB ->
          Cont windowA DA dyadicA ->
            Cont windowB DB dyadicB ->
              Cont DA DB D ->
                Cont D E R ->
                  Cont R S publicRead ->
                    PkgSig bundle dyadicA pkg ->
                      PkgSig bundle dyadicB pkg ->
                        PkgSig bundle D pkg ->
                          PkgSig bundle E pkg ->
                            PkgSig bundle R pkg ->
                              PkgSig bundle S pkg ->
                                PkgSig bundle publicRead pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row publicRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row windowA ∨ hsame row windowB ∨
                                          hsame row dyadicA ∨ hsame row dyadicB ∨
                                            hsame row D ∨ hsame row E ∨ hsame row R ∨
                                              hsame row publicRead)
                                      (fun row : BHist =>
                                        hsame row publicRead ∧ Cont D E R ∧
                                          Cont R S publicRead ∧
                                            PkgSig bundle publicRead pkg)
                                      hsame ∧
                                    UnaryHistory windowA ∧ UnaryHistory windowB ∧
                                      UnaryHistory dyadicA ∧ UnaryHistory dyadicB ∧
                                        UnaryHistory R ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute productRoute
    readbackRoute publicRoute _dyadicAPkg _dyadicBPkg _productPkg _ledgerPkg _readbackPkg
    _sealPkg publicPkg
  obtain ⟨unaryA, unaryB, unaryWA, unaryWB, unaryDA, unaryDB, unaryD, unaryE,
    _unaryR, unaryS, _unaryH, _unaryC, _unaryP, _unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed unaryA unaryWA windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed unaryB unaryWB windowBRoute
  have dyadicAUnary : UnaryHistory dyadicA :=
    unary_cont_closed windowAUnary unaryDA dyadicARoute
  have dyadicBUnary : UnaryHistory dyadicB :=
    unary_cont_closed windowBUnary unaryDB dyadicBRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed unaryD unaryE readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary unaryS publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row dyadicA ∨
              hsame row dyadicB ∨ hsame row D ∨ hsame row E ∨ hsame row R ∨
                hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont D E R ∧ Cont R S publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute, publicRoute, publicPkg⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, dyadicAUnary, dyadicBUnary, rUnary,
      publicUnary⟩

theorem RegularCauchyProductBudget_checked_obligation_readiness [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB publicRead
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont A WA windowA ->
        Cont B WB windowB ->
          Cont windowA DA dyadicA ->
            Cont windowB DB dyadicB ->
              Cont D E R ->
                Cont R S publicRead ->
                  Cont publicRead H obligationRead ->
                    PkgSig bundle obligationRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row windowA ∨ hsame row windowB ∨
                              hsame row dyadicA ∨ hsame row dyadicB ∨ hsame row R ∨
                                hsame row publicRead ∨ hsame row obligationRead)
                          (fun row : BHist =>
                            PkgSig bundle obligationRead pkg ∧ hsame row obligationRead)
                          hsame ∧
                        UnaryHistory windowA ∧ UnaryHistory windowB ∧
                          UnaryHistory dyadicA ∧ UnaryHistory dyadicB ∧
                            UnaryHistory publicRead ∧ UnaryHistory obligationRead ∧
                              Cont publicRead H obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute readbackRoute
    publicRoute obligationRoute obligationPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary, _rUnary,
    sUnary, hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have dyadicAUnary : UnaryHistory dyadicA :=
    unary_cont_closed windowAUnary daUnary dyadicARoute
  have dyadicBUnary : UnaryHistory dyadicB :=
    unary_cont_closed windowBUnary dbUnary dyadicBRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed dUnary eUnary readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary sUnary publicRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed publicUnary hUnary obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row dyadicA ∨
              hsame row dyadicB ∨ hsame row R ∨ hsame row publicRead ∨
                hsame row obligationRead)
          (fun row : BHist => PkgSig bundle obligationRead pkg ∧
            hsame row obligationRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead ⟨hsame_refl obligationRead, obligationUnary⟩
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
      exact ⟨obligationPkg, source.left⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, dyadicAUnary, dyadicBUnary, publicUnary,
      obligationUnary, obligationRoute⟩

theorem RegularCauchyProductBudget_public_export [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont E R publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
                  hsame row D ∨ hsame row E ∨ hsame row R ∨ hsame row S ∨
                    hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ PkgSig bundle publicRead pkg ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory publicRead ∧ Cont E R publicRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, _dUnary,
    eUnary, rUnary, _sUnary, _hUnary, _cUnary, _pUnary, _nUnary, provenancePkg,
    namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed eUnary rUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
              hsame row D ∨ hsame row E ∨ hsame row R ∨ hsame row S ∨
                hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary, publicRoute, provenancePkg, namePkg⟩

theorem RegularCauchyProductBudgetCarrier_dyadic_multiplication_scope [AskSetup]
    [PackageSetup]
    {A B WA WB DA DB D E R S H C P N leftWindow rightWindow dyadicProduct budgetRead
      handoffRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg →
      Cont WA WB leftWindow →
        Cont DA DB rightWindow →
          Cont leftWindow rightWindow dyadicProduct →
            Cont dyadicProduct E budgetRead →
              Cont budgetRead R handoffRead →
                Cont handoffRead S sealRead →
                  PkgSig bundle P pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row WA ∨ hsame row WB ∨ hsame row DA ∨
                            hsame row DB ∨ hsame row D ∨ hsame row E ∨
                              hsame row R ∨ hsame row S ∨
                                hsame row dyadicProduct ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont leftWindow rightWindow dyadicProduct ∧
                            Cont dyadicProduct E budgetRead ∧
                              Cont budgetRead R handoffRead ∧
                                Cont handoffRead S sealRead ∧ PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                        UnaryHistory dyadicProduct ∧ UnaryHistory budgetRead ∧
                          UnaryHistory handoffRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute productRoute budgetRoute handoffRoute sealRoute
    provenancePkg
  obtain ⟨_aUnary, _bUnary, waUnary, wbUnary, daUnary, dbUnary, _dUnary, eUnary,
    rUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _carrierProvenancePkg,
    _namePkg⟩ := carrier
  have leftUnary : UnaryHistory leftWindow :=
    unary_cont_closed waUnary wbUnary leftRoute
  have rightUnary : UnaryHistory rightWindow :=
    unary_cont_closed daUnary dbUnary rightRoute
  have productUnary : UnaryHistory dyadicProduct :=
    unary_cont_closed leftUnary rightUnary productRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed productUnary eUnary budgetRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed budgetUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row WA ∨ hsame row WB ∨ hsame row DA ∨ hsame row DB ∨
              hsame row D ∨ hsame row E ∨ hsame row R ∨ hsame row S ∨
                hsame row dyadicProduct ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont leftWindow rightWindow dyadicProduct ∧
              Cont dyadicProduct E budgetRead ∧ Cont budgetRead R handoffRead ∧
                Cont handoffRead S sealRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                      (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, productRoute, budgetRoute, handoffRoute, sealRoute,
          provenancePkg⟩
  }
  exact
    ⟨cert, leftUnary, rightUnary, productUnary, budgetUnary, handoffUnary,
      sealUnary⟩

end BEDC.Derived.RegularCauchyProductBudgetUp

import BEDC.Derived.RegularCauchyProductBudgetUp.ProductClosureBudget

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_falsifiable_prediction [AskSetup] [PackageSetup]
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
                    PkgSig bundle E pkg ->
                      PkgSig bundle publicRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row windowA ∨ hsame row windowB ∨ hsame row E ∨
                                hsame row publicRead)
                            (fun row : BHist =>
                              hsame row publicRead ∧ Cont D E R ∧
                                Cont R S publicRead ∧ PkgSig bundle E pkg ∧
                                  PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory windowA ∧ UnaryHistory windowB ∧
                            UnaryHistory E ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowARoute windowBRoute _dyadicARoute _dyadicBRoute _productRoute
    readbackRoute publicRoute ledgerPkg publicPkg
  obtain ⟨unaryA, unaryB, unaryWA, unaryWB, _unaryDA, _unaryDB, unaryD, unaryE,
    _unaryR, unaryS, _unaryH, _unaryC, _unaryP, _unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed unaryA unaryWA windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed unaryB unaryWB windowBRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed unaryD unaryE readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary unaryS publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row E ∨
              hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont D E R ∧ Cont R S publicRead ∧
              PkgSig bundle E pkg ∧ PkgSig bundle publicRead pkg)
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute, publicRoute, ledgerPkg, publicPkg⟩
  }
  exact ⟨cert, windowAUnary, windowBUnary, unaryE, publicUnary⟩

end BEDC.Derived.RegularCauchyProductBudgetUp

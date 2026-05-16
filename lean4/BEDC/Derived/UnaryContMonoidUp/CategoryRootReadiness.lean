import BEDC.Derived.UnaryContMonoidUp

namespace BEDC.Derived.UnaryContMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UnaryContMonoidCarrier_category_root_readiness [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name categoryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont ab ledger categoryRead ->
        PkgSig bundle categoryRead pkg ->
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory ab ∧ UnaryHistory ledger ∧
            UnaryHistory categoryRead ∧ Cont a b ab ∧ Cont ab name ledger ∧
              Cont ab ledger categoryRead ∧ hsame e BHist.Empty ∧
                PkgSig bundle ledger pkg ∧ PkgSig bundle categoryRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row categoryRead ∧ UnaryHistory row)
                    (fun row : BHist => Cont ab ledger row ∧ hsame e BHist.Empty)
                    (fun row : BHist =>
                      hsame row categoryRead ∧ PkgSig bundle categoryRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute categoryPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, _leftUnitRoute, _rightUnitRoute,
    ledgerRoute, ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryProduct unaryLedger categoryRoute
  have sourceCategory :
      (fun row : BHist => hsame row categoryRead ∧ UnaryHistory row) categoryRead := by
    exact ⟨hsame_refl categoryRead, unaryCategoryRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row categoryRead ∧ UnaryHistory row)
        (fun row : BHist => Cont ab ledger row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row categoryRead ∧ PkgSig bundle categoryRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro categoryRead sourceCategory
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
          ⟨cont_result_hsame_transport categoryRoute (hsame_symm source.left),
            sameUnit⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, categoryPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryProduct, unaryLedger, unaryCategoryRead, productRoute,
      ledgerRoute, categoryRoute, sameUnit, ledgerPkg, categoryPkg, cert⟩

end BEDC.Derived.UnaryContMonoidUp

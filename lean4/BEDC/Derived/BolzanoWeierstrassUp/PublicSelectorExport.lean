import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassPublicSelectorExport [AskSetup] [PackageSetup]
    {S K R Q E H C P N selector cluster publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K selector ->
        Cont selector R Q ->
          Cont Q E cluster ->
            Cont cluster H publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                        hsame row E ∨ hsame row selector ∨ hsame row cluster ∨
                          hsame row publicRead)
                    (fun row : BHist => PkgSig bundle publicRead pkg ∧ UnaryHistory row)
                    hsame ∧
                  UnaryHistory selector ∧ UnaryHistory cluster ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier selectorRoute readbackRoute clusterRoute publicRoute publicPkg
  have publicPackage :=
    BolzanoWeierstrassPublicNonescapePackage carrier selectorRoute readbackRoute
      clusterRoute publicRoute publicPkg
  obtain ⟨_SUnary, _KUnary, _RUnary, _QUnary, _EUnary, selectorUnary, clusterUnary,
    publicUnary, _selectorRoute, _readbackRoute, _clusterRoute, _publicRoute,
    _carrierPkg, _publicPkg⟩ := publicPackage
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
            hsame row selector ∨ hsame row cluster ∨ hsame row publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg ∧ UnaryHistory row)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.right⟩
    }
  exact ⟨cert, selectorUnary, clusterUnary, publicUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp

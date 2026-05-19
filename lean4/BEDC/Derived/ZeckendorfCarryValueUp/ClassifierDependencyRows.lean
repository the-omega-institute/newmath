import BEDC.Derived.ZeckendorfCarryValueUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZeckendorfCarryValueUp_classifier_dependency_rows [AskSetup] [PackageSetup]
    {source target carry sourceNormal targetNormal valueRow boundary route provenance _nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory target ->
        UnaryHistory carry ->
          UnaryHistory sourceNormal ->
            UnaryHistory targetNormal ->
              UnaryHistory valueRow ->
                UnaryHistory boundary ->
                  UnaryHistory provenance ->
                    Cont carry valueRow route ->
                      Cont route boundary publicRead ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle publicRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row source ∨ hsame row target ∨
                                    hsame row carry ∨ hsame row sourceNormal ∨
                                      hsame row targetNormal ∨ hsame row boundary ∨
                                        hsame row publicRead)
                                (fun row : BHist =>
                                  hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                                hsame ∧
                              UnaryHistory route ∧ UnaryHistory publicRead ∧
                                Cont carry valueRow route ∧ Cont route boundary publicRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert UnaryHistory
  intro _sourceUnary _targetUnary carryUnary _sourceNormalUnary _targetNormalUnary
    valueRowUnary boundaryUnary _provenanceUnary carryValueRoute routeBoundaryPublic
    provenancePkg publicReadPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed carryUnary valueRowUnary carryValueRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary boundaryUnary routeBoundaryPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row source ∨ hsame row target ∨ hsame row carry ∨
            hsame row sourceNormal ∨ hsame row targetNormal ∨ hsame row boundary ∨
              hsame row publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicReadUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceData
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceData.left)
            (unary_transport sourceData.right sameRows)
    }
    pattern_sound := by
      intro row sourceData
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceData.left)))))
    ledger_sound := by
      intro row sourceData
      exact And.intro sourceData.left publicReadPkg
  }
  exact
    ⟨cert, routeUnary, publicReadUnary, carryValueRoute, routeBoundaryPublic, provenancePkg,
      publicReadPkg⟩

end BEDC.Derived.ZeckendorfCarryValueUp

import BEDC.Derived.RieszRepresentationUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationMeasureRowObligation [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName measureRow
      realRow integrationRow representationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg ->
      Cont representing ledger measureRow ->
        Cont measureRow target realRow ->
          Cont realRow boundary integrationRow ->
            Cont integrationRow localName representationRead ->
              PkgSig bundle representationRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row representationRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row measureRow ∨ hsame row realRow ∨
                        hsame row integrationRow ∨ hsame row representationRead ∨
                          hsame row representing ∨ hsame row ledger ∨ hsame row boundary)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont representing ledger measureRow ∧
                        Cont measureRow target realRow ∧
                          Cont realRow boundary integrationRow ∧
                            Cont integrationRow localName representationRead ∧
                              PkgSig bundle representationRead pkg)
                    hsame ∧
                  UnaryHistory measureRow ∧ UnaryHistory realRow ∧
                    UnaryHistory representationRead := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier measureRoute realRoute integrationRoute representationRoute representationPkg
  obtain ⟨_sourceUnary, targetUnary, _functionalUnary, representingUnary, ledgerUnary,
    boundaryUnary, _provenanceUnary, localNameUnary, _carrierRepresentationRoute,
    _carrierBoundaryRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have measureUnary : UnaryHistory measureRow :=
    unary_cont_closed representingUnary ledgerUnary measureRoute
  have realUnary : UnaryHistory realRow :=
    unary_cont_closed measureUnary targetUnary realRoute
  have integrationUnary : UnaryHistory integrationRow :=
    unary_cont_closed realUnary boundaryUnary integrationRoute
  have representationUnary : UnaryHistory representationRead :=
    unary_cont_closed integrationUnary localNameUnary representationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row representationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row measureRow ∨ hsame row realRow ∨ hsame row integrationRow ∨
              hsame row representationRead ∨ hsame row representing ∨ hsame row ledger ∨
                hsame row boundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont representing ledger measureRow ∧
              Cont measureRow target realRow ∧ Cont realRow boundary integrationRow ∧
                Cont integrationRow localName representationRead ∧
                  PkgSig bundle representationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro representationRead
        ⟨hsame_refl representationRead, representationUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, measureRoute, realRoute, integrationRoute, representationRoute,
          representationPkg⟩
  }
  exact ⟨cert, measureUnary, realUnary, representationUnary⟩

end BEDC.Derived.RieszRepresentationUp

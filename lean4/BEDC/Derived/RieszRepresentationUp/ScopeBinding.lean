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

theorem RieszRepresentationScopeBinding [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName banachRead
      hilbertRead measureRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg →
      Cont source functional banachRead →
        Cont functional representing hilbertRead →
          Cont ledger boundary measureRead →
            Cont hilbertRead measureRead branchRead →
              PkgSig bundle banachRead pkg →
                PkgSig bundle hilbertRead pkg →
                  PkgSig bundle measureRead pkg →
                    PkgSig bundle branchRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row functional ∨
                              hsame row representing ∨ hsame row ledger ∨
                                hsame row boundary ∨ hsame row banachRead ∨
                                  hsame row hilbertRead ∨ hsame row measureRead ∨
                                    hsame row branchRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont source functional banachRead ∧
                              Cont functional representing hilbertRead ∧
                                Cont ledger boundary measureRead ∧
                                  Cont hilbertRead measureRead branchRead ∧
                                    PkgSig bundle branchRead pkg)
                          hsame ∧
                        UnaryHistory banachRead ∧ UnaryHistory hilbertRead ∧
                          UnaryHistory measureRead ∧ UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows banachRoute hilbertRoute measureRoute branchRoute _banachPkg
    _hilbertPkg _measurePkg branchPkg
  obtain ⟨sourceUnary, _targetUnary, functionalUnary, representingUnary, ledgerUnary,
    boundaryUnary, _provenanceUnary, _localNameUnary, _representationRoute,
    _boundaryRoute, _provenancePkg, _localNamePkg⟩ := carrierRows
  have banachUnary : UnaryHistory banachRead :=
    unary_cont_closed sourceUnary functionalUnary banachRoute
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed functionalUnary representingUnary hilbertRoute
  have measureUnary : UnaryHistory measureRead :=
    unary_cont_closed ledgerUnary boundaryUnary measureRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed hilbertUnary measureUnary branchRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row functional ∨ hsame row representing ∨
              hsame row ledger ∨ hsame row boundary ∨ hsame row banachRead ∨
                hsame row hilbertRead ∨ hsame row measureRead ∨ hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source functional banachRead ∧
              Cont functional representing hilbertRead ∧ Cont ledger boundary measureRead ∧
                Cont hilbertRead measureRead branchRead ∧ PkgSig bundle branchRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead ⟨hsame_refl branchRead, branchUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, banachRoute, hilbertRoute, measureRoute, branchRoute,
          branchPkg⟩
  }
  exact ⟨cert, banachUnary, hilbertUnary, measureUnary, branchUnary⟩

end BEDC.Derived.RieszRepresentationUp

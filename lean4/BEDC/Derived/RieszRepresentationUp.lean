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
    {source target functional representing ledger boundary provenance localName hilbertRead
      measureRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg →
      Cont source functional hilbertRead →
        Cont representing boundary measureRead →
          Cont hilbertRead measureRead scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row functional ∨ hsame row representing ∨
                      hsame row boundary ∨ hsame row hilbertRead ∨ hsame row measureRead ∨
                        hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont source functional hilbertRead ∧
                      Cont representing boundary measureRead ∧
                        Cont hilbertRead measureRead scopedRead ∧ PkgSig bundle scopedRead pkg)
                  hsame ∧
                UnaryHistory hilbertRead ∧ UnaryHistory measureRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows hilbertRoute measureRoute scopedRoute scopedPkg
  obtain ⟨sourceUnary, _targetUnary, functionalUnary, representingUnary, _ledgerUnary,
    boundaryUnary, _provenanceUnary, _localNameUnary, _functionalRepresentingLedger,
    _sourceTargetBoundary, _provenancePkg, _localNamePkg⟩ := carrierRows
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed sourceUnary functionalUnary hilbertRoute
  have measureUnary : UnaryHistory measureRead :=
    unary_cont_closed representingUnary boundaryUnary measureRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed hilbertUnary measureUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row functional ∨ hsame row representing ∨
              hsame row boundary ∨ hsame row hilbertRead ∨ hsame row measureRead ∨
                hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source functional hilbertRead ∧
              Cont representing boundary measureRead ∧ Cont hilbertRead measureRead scopedRead ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, hilbertRoute, measureRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, hilbertUnary, measureUnary, scopedUnary⟩

end BEDC.Derived.RieszRepresentationUp

import BEDC.Derived.RieszRepresentationUp.TasteGate
import BEDC.Derived.RieszRepresentationUp.ScopeBinding
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationRealSealObligation [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName hilbertRead
      measureRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg →
      Cont functional representing hilbertRead →
        Cont ledger boundary measureRead →
          Cont hilbertRead measureRead realSealRead →
            PkgSig bundle realSealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row target ∨ hsame row functional ∨
                      hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                        hsame row hilbertRead ∨ hsame row measureRead ∨
                          hsame row realSealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont functional representing hilbertRead ∧
                      Cont ledger boundary measureRead ∧
                        Cont hilbertRead measureRead realSealRead ∧
                          PkgSig bundle realSealRead pkg)
                  hsame ∧
                UnaryHistory hilbertRead ∧ UnaryHistory measureRead ∧
                  UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows hilbertRoute measureRoute realSealRoute realSealPkg
  obtain ⟨_sourceUnary, _targetUnary, functionalUnary, representingUnary, ledgerUnary,
    boundaryUnary, _provenanceUnary, _localNameUnary, _representationRoute,
    _boundaryRoute, _provenancePkg, _localNamePkg⟩ := carrierRows
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed functionalUnary representingUnary hilbertRoute
  have measureUnary : UnaryHistory measureRead :=
    unary_cont_closed ledgerUnary boundaryUnary measureRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed hilbertUnary measureUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row functional ∨
              hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                hsame row hilbertRead ∨ hsame row measureRead ∨ hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont functional representing hilbertRead ∧
              Cont ledger boundary measureRead ∧ Cont hilbertRead measureRead realSealRead ∧
                PkgSig bundle realSealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSealRead
        ⟨hsame_refl realSealRead, realSealUnary⟩
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
      exact ⟨sourceRow.right, hilbertRoute, measureRoute, realSealRoute, realSealPkg⟩
  }
  exact ⟨cert, hilbertUnary, measureUnary, realSealUnary⟩

end BEDC.Derived.RieszRepresentationUp

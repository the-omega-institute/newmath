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

theorem RieszRepresentationBranchBoundaryNonescape [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName hilbertRead
      measureRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg ->
      Cont representing boundary hilbertRead ->
        Cont ledger boundary measureRead ->
          Cont hilbertRead measureRead branchRead ->
            PkgSig bundle branchRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row functional ∨ hsame row representing ∨
                      hsame row ledger ∨ hsame row boundary ∨ hsame row branchRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont representing boundary hilbertRead ∧
                      Cont ledger boundary measureRead ∧ PkgSig bundle branchRead pkg)
                  hsame ∧
                UnaryHistory hilbertRead ∧ UnaryHistory measureRead ∧
                  UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier representingBoundary ledgerBoundary branchRoute branchPkg
  have representingUnary : UnaryHistory representing := carrier.right.right.right.left
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.right.left
  have boundaryUnary : UnaryHistory boundary := carrier.right.right.right.right.right.left
  have hilbertReadUnary : UnaryHistory hilbertRead :=
    unary_cont_closed representingUnary boundaryUnary representingBoundary
  have measureReadUnary : UnaryHistory measureRead :=
    unary_cont_closed ledgerUnary boundaryUnary ledgerBoundary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed hilbertReadUnary measureReadUnary branchRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row functional ∨ hsame row representing ∨
              hsame row ledger ∨ hsame row boundary ∨ hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont representing boundary hilbertRead ∧
              Cont ledger boundary measureRead ∧ PkgSig bundle branchRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro branchRead
          ⟨hsame_refl branchRead, branchReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, representingBoundary, ledgerBoundary, branchPkg⟩
    }
  exact ⟨cert, hilbertReadUnary, measureReadUnary, branchReadUnary⟩

end BEDC.Derived.RieszRepresentationUp

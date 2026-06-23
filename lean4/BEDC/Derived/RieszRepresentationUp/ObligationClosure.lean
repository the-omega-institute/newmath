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

theorem RieszRepresentationObligationClosure [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName measureRoute
      banachRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg →
      Cont source target banachRoute →
        Cont representing boundary measureRoute →
          SemanticNameCert
              (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row functional ∨
                  hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row measureRoute ∨
                      hsame row banachRoute)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont functional representing ledger ∧
                  Cont source target boundary ∧ Cont source target banachRoute ∧
                    Cont representing boundary measureRoute ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory ledger := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrierRows banachRouteCont measureRouteCont
  obtain ⟨_sourceUnary, _targetUnary, _functionalUnary, _representingUnary, ledgerUnary,
    _boundaryUnary, _provenanceUnary, _localNameUnary, representationRoute, boundaryRoute,
    provenancePkg, localNamePkg⟩ := carrierRows
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row functional ∨
              hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row measureRoute ∨
                  hsame row banachRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont functional representing ledger ∧
              Cont source target boundary ∧ Cont source target banachRoute ∧
                Cont representing boundary measureRoute ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger ⟨hsame_refl ledger, ledgerUnary⟩
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
      right
      right
      right
      right
      left
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, representationRoute, boundaryRoute, banachRouteCont,
          measureRouteCont, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.RieszRepresentationUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedCauchyFilterCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedCauchyFilterCompletionCarrier [AskSetup] [PackageSetup]
    (completionSource filterBase boundLedger stream tolerance readback realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory completionSource ∧ UnaryHistory filterBase ∧ UnaryHistory boundLedger ∧
    UnaryHistory stream ∧ UnaryHistory tolerance ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem BoundedCauchyFilterCompletionNameCertObligations [AskSetup] [PackageSetup]
    {completionSource filterBase boundLedger stream tolerance readback realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedCauchyFilterCompletionCarrier completionSource filterBase boundLedger stream tolerance
        readback realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BoundedCauchyFilterCompletionCarrier completionSource filterBase boundLedger stream
              tolerance readback realSeal transport replay provenance localName bundle pkg ∧
            hsame row localName ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row completionSource ∨ hsame row filterBase ∨ hsame row boundLedger ∨
            hsame row stream ∨ hsame row tolerance ∨ hsame row readback ∨
              hsame row realSeal ∨ hsame row localName)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_completionSourceUnary, _filterBaseUnary, _boundLedgerUnary, _streamUnary,
    _toleranceUnary, _readbackUnary, _realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierWitness, hsame_refl localName, localNameUnary⟩
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
          ⟨sourceRow.left,
            hsame_trans (hsame_symm sameRows) sourceRow.right.left,
            unary_transport sourceRow.right.right sameRows⟩
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
                    (Or.inr sourceRow.right.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, provenancePkg, localNamePkg⟩
  }

end BEDC.Derived.BoundedCauchyFilterCompletionUp

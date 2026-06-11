import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactPolishUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocallyCompactPolishCarrier [AskSetup] [PackageSetup]
    (source localCompact compactLedger completeSeparable polish proper sigma stream rat
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory localCompact ∧ UnaryHistory compactLedger ∧
    UnaryHistory completeSeparable ∧ UnaryHistory polish ∧ UnaryHistory proper ∧
      UnaryHistory sigma ∧ UnaryHistory stream ∧ UnaryHistory rat ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem LocallyCompactPolishNameCertObligations [AskSetup] [PackageSetup]
    {source localCompact compactLedger completeSeparable polish proper sigma stream rat transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocallyCompactPolishCarrier source localCompact compactLedger completeSeparable polish proper
        sigma stream rat transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocallyCompactPolishCarrier source localCompact compactLedger completeSeparable polish
              proper sigma stream rat transport replay provenance localName bundle pkg ∧
            hsame row localName ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row source ∨ hsame row localCompact ∨ hsame row compactLedger ∨
            hsame row completeSeparable ∨ hsame row polish ∨ hsame row proper ∨
              hsame row sigma ∨ hsame row stream ∨ hsame row rat ∨ hsame row localName)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _localCompactUnary, _compactLedgerUnary, _completeSeparableUnary,
    _polishUnary, _properUnary, _sigmaUnary, _streamUnary, _ratUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, provenancePkg, localNamePkg⟩ := carrier
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
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.right.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, provenancePkg, localNamePkg⟩
  }

end BEDC.Derived.LocallyCompactPolishUp

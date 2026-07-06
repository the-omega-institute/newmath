import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ActiveReadingGateCarrier_scope_grounding_carrier [AskSetup] [PackageSetup]
    (target active retired blocking exportRow transport replay provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory target ∧ UnaryHistory active ∧ UnaryHistory retired ∧ UnaryHistory blocking ∧
    UnaryHistory exportRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont target active blocking ∧
        Cont blocking exportRow provenance ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle nameCert pkg

theorem ActiveReadingGateCarrier_scope_grounding [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert scopeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ActiveReadingGateCarrier_scope_grounding_carrier target active retired blocking exportRow
        transport replay provenance nameCert bundle pkg →
      Cont target active blocking →
        Cont blocking exportRow scopeRead →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row scopeRead ∧
                    ActiveReadingGateCarrier_scope_grounding_carrier target active retired
                      blocking exportRow transport replay provenance nameCert bundle pkg)
                (fun row : BHist =>
                  hsame row target ∨ hsame row active ∨ hsame row retired ∨
                    hsame row blocking ∨ hsame row exportRow ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row nameCert ∨
                        hsame row scopeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont target active blocking ∧
                    Cont blocking exportRow scopeRead ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier targetActive blockingExport provenancePkg
  have carrierProof :
      ActiveReadingGateCarrier_scope_grounding_carrier target active retired blocking exportRow
        transport replay provenance nameCert bundle pkg :=
    carrier
  obtain
    ⟨targetUnary, activeUnary, retiredUnary, blockingUnary, exportUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, _carrierTargetActive, _carrierExport,
      _carrierProvenance, _carrierName⟩ := carrier
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed blockingUnary exportUnary blockingExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row scopeRead ∧
              ActiveReadingGateCarrier_scope_grounding_carrier target active retired blocking
                exportRow transport replay provenance nameCert bundle pkg)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row retired ∨ hsame row blocking ∨
              hsame row exportRow ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row nameCert ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active blocking ∧ Cont blocking exportRow scopeRead ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, carrierProof⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport scopeUnary (hsame_symm source.left)
      exact ⟨rowUnary, targetActive, blockingExport, provenancePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

end BEDC.Derived.ActiveReadingGateUp

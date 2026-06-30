import BEDC.Derived.PhysicalLawBridgeUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def PhysicalLawBridgeCarrier
    (law empirical bridge object fit failure transport replay provenance name : BHist) :
    Prop :=
  UnaryHistory law ∧ UnaryHistory empirical ∧ UnaryHistory bridge ∧
    UnaryHistory object ∧ UnaryHistory fit ∧ UnaryHistory failure ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont law empirical bridge ∧ Cont object fit failure ∧
          Cont transport replay provenance

theorem PhysicalLawBridgeCarrier_namecert_surface
    {law empirical bridge object fit failure transport replay provenance name nameRead : BHist} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay provenance
        name →
      Cont replay provenance nameRead →
        hsame nameRead name →
          SemanticNameCert
              (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                  hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                    hsame row nameRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont replay provenance nameRead ∧ hsame nameRead name)
              hsame ∧
            UnaryHistory nameRead ∧ hsame nameRead name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PhysicalLawBridgeCarrier
  intro carrier replayProvenanceName sameName
  obtain ⟨_lawUnary, _empiricalUnary, _bridgeUnary, _objectUnary, _fitUnary,
    _failureUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _lawEmpiricalBridge, _objectFitFailure, _transportReplayProvenance⟩ := carrier
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenanceName
  have sourceNameRead :
      (fun row : BHist => hsame row nameRead ∧ UnaryHistory row) nameRead := by
    exact ⟨hsame_refl nameRead, nameReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance nameRead ∧ hsame nameRead name)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead sourceNameRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayProvenanceName, sameName⟩
  }
  exact ⟨cert, nameReadUnary, sameName⟩

end BEDC.Derived.PhysicalLawBridgeUp

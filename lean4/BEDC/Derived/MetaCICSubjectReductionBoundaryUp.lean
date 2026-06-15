import BEDC.Derived.MetaCICSubjectReductionBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICSubjectReductionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def MetaCICSubjectReductionBoundaryCarrier
    (beta app lam pi theoremRow obstruction audit transport route provenance localName : BHist) :
    Prop :=
  UnaryHistory beta ∧ UnaryHistory app ∧ UnaryHistory lam ∧ UnaryHistory pi ∧
    UnaryHistory theoremRow ∧ UnaryHistory obstruction ∧ UnaryHistory audit ∧
      UnaryHistory transport ∧ Cont beta app transport ∧
        Cont lam pi route ∧ Cont transport route theoremRow

theorem MetaCICSubjectReductionBoundaryCarrier_obligation_exposure_certificate
    {beta app lam pi theoremRow obstruction audit transport route provenance localName
      exposureRead preservationRead : BHist} :
    MetaCICSubjectReductionBoundaryCarrier beta app lam pi theoremRow obstruction audit
        transport route provenance localName ->
      Cont beta app exposureRead ->
        Cont exposureRead theoremRow preservationRead ->
          SemanticNameCert
              (fun row : BHist => hsame row preservationRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row preservationRead)
              (fun row : BHist =>
                hsame row preservationRead ∧ Cont exposureRead theoremRow preservationRead)
              hsame ∧
            UnaryHistory exposureRead ∧ UnaryHistory preservationRead ∧
              Cont beta app exposureRead ∧ Cont exposureRead theoremRow preservationRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier betaAppExposure exposureTheoremPreservation
  obtain
    ⟨betaUnary, appUnary, _lamUnary, _piUnary, theoremUnary, _obstructionUnary,
      _auditUnary, _transportUnary, _betaAppTransport, _lamPiRoute,
      _transportRouteTheorem⟩ := carrier
  have exposureUnary : UnaryHistory exposureRead :=
    unary_cont_closed betaUnary appUnary betaAppExposure
  have preservationUnary : UnaryHistory preservationRead :=
    unary_cont_closed exposureUnary theoremUnary exposureTheoremPreservation
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row preservationRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row preservationRead)
          (fun row : BHist =>
            hsame row preservationRead ∧ Cont exposureRead theoremRow preservationRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro preservationRead
        (And.intro (hsame_refl preservationRead) preservationUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left exposureTheoremPreservation
  }
  exact
    ⟨cert, exposureUnary, preservationUnary, betaAppExposure,
      exposureTheoremPreservation⟩

end BEDC.Derived.MetaCICSubjectReductionBoundaryUp

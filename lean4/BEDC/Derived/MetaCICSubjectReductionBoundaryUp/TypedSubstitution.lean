import BEDC.Derived.MetaCICSubjectReductionBoundaryUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICSubjectReductionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetaCICSubjectReductionBoundaryCarrier_typed_substitution
    {beta app lam pi theoremRow obstruction audit transport route provenance localName exposureRead
      preservationRead typedRead : BHist} :
    MetaCICSubjectReductionBoundaryCarrier beta app lam pi theoremRow obstruction audit transport
        route provenance localName ->
      Cont beta app exposureRead ->
        Cont exposureRead theoremRow preservationRead ->
          Cont preservationRead audit typedRead ->
            SemanticNameCert
                (fun row : BHist => hsame row typedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row beta ∨ hsame row app ∨ hsame row lam ∨ hsame row pi ∨
                    hsame row theoremRow ∨ hsame row audit ∨ hsame row typedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont beta app exposureRead ∧
                    Cont exposureRead theoremRow preservationRead ∧
                      Cont preservationRead audit typedRead)
                hsame ∧
              UnaryHistory exposureRead ∧ UnaryHistory preservationRead ∧
                UnaryHistory typedRead := by
  -- BEDC touchpoint anchor: MetaCICSubjectReductionBoundaryCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier exposureRoute preservationRoute typedRoute
  obtain ⟨betaUnary, appUnary, _lamUnary, _piUnary, theoremUnary, _obstructionUnary,
    auditUnary, _transportUnary, _betaAppTransport, _lamPiRoute, _transportRouteTheorem⟩ :=
    carrier
  have exposureUnary : UnaryHistory exposureRead :=
    unary_cont_closed betaUnary appUnary exposureRoute
  have preservationUnary : UnaryHistory preservationRead :=
    unary_cont_closed exposureUnary theoremUnary preservationRoute
  have typedUnary : UnaryHistory typedRead :=
    unary_cont_closed preservationUnary auditUnary typedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row typedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row beta ∨ hsame row app ∨ hsame row lam ∨ hsame row pi ∨
              hsame row theoremRow ∨ hsame row audit ∨ hsame row typedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont beta app exposureRead ∧
              Cont exposureRead theoremRow preservationRead ∧
                Cont preservationRead audit typedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro typedRead ⟨hsame_refl typedRead, typedUnary⟩
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
      exact ⟨source.right, exposureRoute, preservationRoute, typedRoute⟩
  }
  exact ⟨cert, exposureUnary, preservationUnary, typedUnary⟩

end BEDC.Derived.MetaCICSubjectReductionBoundaryUp

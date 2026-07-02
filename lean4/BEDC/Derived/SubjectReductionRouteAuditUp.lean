import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

inductive SubjectReductionRouteAuditUp : Type where
  | mk
      (bundle exactness invocation handoff socket transport replay provenance localName :
        BHist) : SubjectReductionRouteAuditUp
deriving DecidableEq

namespace SubjectReductionRouteAuditUp

theorem SubjectReductionRouteAudit_obligation_surface
    {B E I U S H C P N socketRead consumerRead : BHist} :
    UnaryHistory B ->
      UnaryHistory E ->
        UnaryHistory I ->
          UnaryHistory U ->
            UnaryHistory S ->
              UnaryHistory P ->
                UnaryHistory N ->
                  hsame H (append B E) ->
                    Cont E U socketRead ->
                      Cont socketRead S consumerRead ->
                        SemanticNameCert
                            (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                            (fun row : BHist => hsame row consumerRead)
                            (fun row : BHist =>
                              hsame row consumerRead ∧ Cont socketRead S consumerRead)
                            hsame ∧
                          UnaryHistory B ∧ UnaryHistory E ∧ UnaryHistory I ∧
                            UnaryHistory U ∧ UnaryHistory S ∧ UnaryHistory socketRead ∧
                              UnaryHistory consumerRead ∧ UnaryHistory P ∧ UnaryHistory N ∧
                                hsame H (append B E) ∧ Cont E U socketRead ∧
                                  Cont socketRead S consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryB unaryE unaryI unaryU unaryS unaryP unaryN sameH socketRoute consumerRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryE unaryU socketRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed socketUnary unaryS consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row consumerRead)
          (fun row : BHist => hsame row consumerRead ∧ Cont socketRead S consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryB, unaryE, unaryI, unaryU, unaryS, socketUnary, consumerUnary, unaryP,
      unaryN, sameH, socketRoute, consumerRoute⟩

end SubjectReductionRouteAuditUp

end BEDC.Derived

import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_classifier_readiness
    {Z S M R Q H C P N classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) H classifierRead ->
        SemanticNameCert
            (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row classifierRead)
            (fun row : BHist =>
              hsame row classifierRead ∧ Cont (append Z S) H classifierRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧
            UnaryHistory classifierRead ∧ hsame H (append Z S) ∧
              Cont (append Z S) H classifierRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryAppend unaryH classifierRoute
  have sourceAtClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row classifierRead)
          (fun row : BHist =>
            hsame row classifierRead ∧ Cont (append Z S) H classifierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceAtClassifier
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
      exact ⟨source.left, classifierRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryH, classifierUnary, sameH, classifierRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp

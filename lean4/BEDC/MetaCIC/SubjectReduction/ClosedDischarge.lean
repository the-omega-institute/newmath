import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.SubjectReduction
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.ClosurePreservation

namespace BEDC.MetaCIC

def closedReducingType : Term :=
  Term.app (Term.lam Term.sort (Term.var 0)) Term.sort

def closedDependentFunction : Term :=
  Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))

def closedDependentCodomain : Term :=
  Term.pi (Term.var 0) (Term.var 1)

def closedDependentApp : Term :=
  Term.app closedDependentFunction closedReducingType

def closedDependentAppReduced : Term :=
  Term.app closedDependentFunction Term.sort

def closedDependentAppType : Term :=
  Term.pi closedReducingType closedReducingType

def closedDependentReducedType : Term :=
  Term.pi Term.sort Term.sort

theorem closedReducingType_typed :
    HasType [] closedReducingType Term.sort := by
  unfold closedReducingType
  exact id_sort_applied

theorem closedReducingType_step :
    BetaStep closedReducingType Term.sort := by
  unfold closedReducingType
  exact BetaStep.beta Term.sort (Term.var 0) Term.sort

theorem closedReducingType_closed :
    ClosedAt 0 closedReducingType := by
  unfold closedReducingType
  apply ClosedAt.appClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
  · exact ClosedAt.sortClosed

theorem closedDependentFunction_typed :
    HasType [] closedDependentFunction
      (Term.pi Term.sort closedDependentCodomain) := by
  unfold closedDependentFunction
  unfold closedDependentCodomain
  apply HasType.lamRule
  · exact HasType.sortRule []
  · exact dependent_identity_tracks_outer_domain

theorem closedDependentFunction_closed :
    ClosedAt 0 closedDependentFunction := by
  unfold closedDependentFunction
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 1

theorem closedDependentCodomain_subst_reducing :
    substitute 0 closedReducingType closedDependentCodomain =
      closedDependentAppType := by
  unfold closedDependentCodomain
  unfold closedDependentAppType
  unfold closedReducingType
  rfl

theorem closedDependentCodomain_subst_reduced :
    substitute 0 Term.sort closedDependentCodomain =
      closedDependentReducedType := by
  unfold closedDependentCodomain
  unfold closedDependentReducedType
  rfl

theorem closedDependentCodomain_subst_changes :
    substitute 0 Term.sort closedDependentCodomain ≠
      substitute 0 closedReducingType closedDependentCodomain := by
  intro h
  rw [closedDependentCodomain_subst_reduced] at h
  rw [closedDependentCodomain_subst_reducing] at h
  unfold closedDependentReducedType at h
  unfold closedDependentAppType at h
  cases h

theorem closedDependentApp_typed :
    HasType [] closedDependentApp closedDependentAppType := by
  unfold closedDependentApp
  rw [← closedDependentCodomain_subst_reducing]
  apply HasType.appRule
  · exact closedDependentFunction_typed
  · exact closedReducingType_typed

theorem closedDependentApp_step :
    BetaStep closedDependentApp closedDependentAppReduced := by
  unfold closedDependentApp
  unfold closedDependentAppReduced
  exact BetaStep.congApp2
    closedDependentFunction
    closedReducingType
    Term.sort
    closedReducingType_step

theorem closedDependentApp_closed :
    ClosedAt 0 closedDependentApp := by
  unfold closedDependentApp
  apply ClosedAt.appClosed
  · exact closedDependentFunction_closed
  · exact closedReducingType_closed

theorem closedDependentAppReduced_typed :
    HasType [] closedDependentAppReduced closedDependentReducedType := by
  unfold closedDependentAppReduced
  rw [← closedDependentCodomain_subst_reduced]
  apply HasType.appRule
  · exact closedDependentFunction_typed
  · exact HasType.sortRule []

theorem closedDependentCodomain_no_sort_subst_to_original_type
    (cod : Term) :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0)) cod →
    substitute 0 Term.sort cod ≠ closedDependentAppType := by
  intro hcod hbad
  cases hcod with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup
          unfold closedDependentAppType at hbad
          unfold closedReducingType at hbad
          cases hbad

theorem closedDependentAppReduced_type_shape {A : Term}
    (h : HasType [] closedDependentAppReduced A) :
    A = closedDependentReducedType := by
  unfold closedDependentAppReduced at h
  unfold closedDependentFunction at h
  cases h with
  | appRule Γ f a dom cod hf ha =>
      cases ha with
      | sortRule Δ =>
          cases hf with
          | lamRule Γ dom body cod hdom hbody =>
              cases hbody with
              | lamRule Γ innerDom innerBody innerCod hinnerDom hinnerBody =>
                  cases hinnerBody with
                  | varRule Γ i A hlookup =>
                      cases hlookup
                      unfold closedDependentReducedType
                      rfl

theorem closedDependentAppReduced_not_original_type :
    ¬ HasType [] closedDependentAppReduced closedDependentAppType := by
  intro h
  have hshape :
      closedDependentAppType = closedDependentReducedType := by
    exact closedDependentAppReduced_type_shape h
  unfold closedDependentAppType at hshape
  unfold closedDependentReducedType at hshape
  unfold closedReducingType at hshape
  cases hshape

theorem appArgTypeStable_closed_independent_codomain :
    ∀ {f a a' dom cod : Term},
    HasType [] f (Term.pi dom cod) →
    HasType [] a dom →
    HasType [] a' dom →
    ClosedAt 0 cod →
    substitute 0 a' cod = substitute 0 a cod := by
  intro f a a' dom cod _hf _ha _ha' hcod
  rw [substitute_closed 0 a' cod hcod]
  rw [substitute_closed 0 a cod hcod]

theorem appArgTypeStable_closed :
    ∀ {f a a' dom cod : Term},
    HasType [] f (Term.pi dom cod) →
    HasType [] a dom →
    HasType [] a' dom →
    ClosedAt 0 f →
    ClosedAt 0 a →
    ClosedAt 0 cod →
    BetaStep a a' →
    substitute 0 a' cod = substitute 0 a cod := by
  intro f a a' dom cod hf ha ha' _hf_closed _ha_closed hcod _hstep
  exact appArgTypeStable_closed_independent_codomain hf ha ha' hcod

theorem subject_reduction_closed_app_independent_codomain :
    ∀ {f a a' dom cod : Term},
    HasType [] f (Term.pi dom cod) →
    HasType [] a dom →
    HasType [] a' dom →
    ClosedAt 0 f →
    ClosedAt 0 a →
    ClosedAt 0 cod →
    BetaStep a a' →
    HasType [] (Term.app f a') (substitute 0 a cod) := by
  intro f a a' dom cod hf ha ha' hf_closed ha_closed hcod hstep
  rw [← appArgTypeStable_closed hf ha ha' hf_closed ha_closed hcod hstep]
  exact HasType.appRule [] f a' dom cod hf ha'

theorem appArgTypeStable_closed_counterexample :
    ∃ f a a' dom cod,
      HasType [] f (Term.pi dom cod) ∧
        HasType [] a dom ∧
          HasType [] a' dom ∧
            ClosedAt 0 f ∧
              ClosedAt 0 a ∧
                BetaStep a a' ∧
                  substitute 0 a' cod ≠ substitute 0 a cod := by
  exact
    ⟨closedDependentFunction,
      closedReducingType,
      Term.sort,
      Term.sort,
      closedDependentCodomain,
      closedDependentFunction_typed,
      closedReducingType_typed,
      HasType.sortRule [],
      closedDependentFunction_closed,
      closedReducingType_closed,
      closedReducingType_step,
      closedDependentCodomain_subst_changes⟩

theorem subject_reduction_closed_app_counterexample :
    ∃ f a t' A,
      HasType [] (Term.app f a) A ∧
        BetaStep (Term.app f a) t' ∧
          ClosedAt 0 (Term.app f a) ∧
            ¬ HasType [] t' A := by
  exact
    ⟨closedDependentFunction,
      closedReducingType,
      closedDependentAppReduced,
      closedDependentAppType,
      closedDependentApp_typed,
      closedDependentApp_step,
      closedDependentApp_closed,
      closedDependentAppReduced_not_original_type⟩

end BEDC.MetaCIC

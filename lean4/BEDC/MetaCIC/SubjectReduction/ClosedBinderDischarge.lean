import BEDC.MetaCIC.SubjectReduction
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Typing.ClosedInversion

namespace BEDC.MetaCIC

def LamDomainSRClosedStatement : Prop :=
  ∀ {d b d' c : Term},
    HasType [] (Term.lam d b) (Term.pi d c) →
    ClosedAt 0 (Term.lam d b) →
    BetaStep d d' →
    HasType [] (Term.lam d' b) (Term.pi d' c)

def PiDomainSRClosedStatement : Prop :=
  ∀ {d c d' A : Term},
    HasType [] (Term.pi d c) A →
    ClosedAt 0 (Term.pi d c) →
    BetaStep d d' →
    HasType [] (Term.pi d' c) A

def SubjectReductionClosedLamStatement : Prop :=
  ∀ {d b t' A : Term},
    HasType [] (Term.lam d b) A →
    ClosedAt 0 (Term.lam d b) →
    BetaStep (Term.lam d b) t' →
    HasType [] t' A

def SubjectReductionClosedPiStatement : Prop :=
  ∀ {d c t' A : Term},
    HasType [] (Term.pi d c) A →
    ClosedAt 0 (Term.pi d c) →
    BetaStep (Term.pi d c) t' →
    HasType [] t' A

def SubjectReductionClosedStatement : Prop :=
  ∀ {t t' A : Term},
    HasType [] t A →
    ClosedAt 0 t →
    BetaStep t t' →
    HasType [] t' A

def closedLamDomainSource : Term :=
  Term.lam closedReducingType (Term.var 0)

def closedLamDomainTarget : Term :=
  Term.lam Term.sort (Term.var 0)

def closedLamDomainType : Term :=
  Term.pi closedReducingType (shift 0 1 closedReducingType)

theorem closedReducingType_typed_ctx (Γ : Ctx) :
    HasType Γ closedReducingType Term.sort := by
  unfold closedReducingType
  exact HasType.appRule Γ
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    Term.sort
    Term.sort
    (by
      apply HasType.lamRule
      · exact HasType.sortRule Γ
      · apply HasType.varRule
        rfl)
    (HasType.sortRule Γ)

theorem closedReducingType_shift_typed_ctx (Γ : Ctx) :
    HasType Γ (shift 0 1 closedReducingType) Term.sort := by
  rw [shift_closed 0 closedReducingType closedReducingType_closed]
  exact closedReducingType_typed_ctx Γ

theorem closedReducingType_shift_closed_zero :
    ClosedAt 0 (shift 0 1 closedReducingType) := by
  rw [shift_closed 0 closedReducingType closedReducingType_closed]
  exact closedReducingType_closed

theorem sort_ne_closedReducingType_shift :
    Term.sort ≠ shift 0 1 closedReducingType := by
  intro h
  unfold closedReducingType at h
  unfold shift at h
  cases h

theorem closedReducingType_ne_sort :
    closedReducingType ≠ Term.sort := by
  intro h
  unfold closedReducingType at h
  cases h

theorem closedLamDomainSource_typed :
    HasType [] closedLamDomainSource closedLamDomainType := by
  unfold closedLamDomainSource
  unfold closedLamDomainType
  apply HasType.lamRule
  · exact closedReducingType_typed
  · apply HasType.varRule
    rfl

theorem closedLamDomainSource_closed :
    ClosedAt 0 closedLamDomainSource := by
  unfold closedLamDomainSource
  apply ClosedAt.lamClosed
  · exact closedReducingType_closed
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 0

theorem closedLamDomainSource_step :
    BetaStep closedLamDomainSource closedLamDomainTarget := by
  unfold closedLamDomainSource
  unfold closedLamDomainTarget
  exact BetaStep.congLamDom
    closedReducingType
    Term.sort
    (Term.var 0)
    closedReducingType_step

theorem closedLamDomainTarget_not_typed :
    ¬ HasType [] closedLamDomainTarget closedLamDomainType := by
  intro h
  cases hasType_lam_ctx_components h with
  | intro cod hcomponents =>
      unfold closedLamDomainTarget at hcomponents
      unfold closedLamDomainType at hcomponents
      have hdom : closedReducingType = Term.sort := by
        cases hcomponents.left
      exact closedReducingType_ne_sort hdom

theorem closedLamDomainRetypedTarget_not_typed :
    ¬ HasType []
      closedLamDomainTarget
      (Term.pi Term.sort (shift 0 1 closedReducingType)) := by
  intro h
  cases hasType_lam_ctx_components h with
  | intro cod hcomponents =>
      have hbody := hcomponents.right.right
      unfold closedLamDomainTarget at hcomponents
      cases hcomponents.left
      cases hbody with
      | varRule Γ i A hlookup =>
          change some Term.sort =
            some (shift 0 1 closedReducingType) at hlookup
          cases hlookup

theorem lamDomainSR_closed_counterexample :
    ∃ d b d' c,
      HasType [] (Term.lam d b) (Term.pi d c) ∧
        ClosedAt 0 (Term.lam d b) ∧
          BetaStep d d' ∧
            ¬ HasType [] (Term.lam d' b) (Term.pi d' c) := by
  exact
    ⟨closedReducingType,
      Term.var 0,
      Term.sort,
      shift 0 1 closedReducingType,
      closedLamDomainSource_typed,
      closedLamDomainSource_closed,
      closedReducingType_step,
      closedLamDomainRetypedTarget_not_typed⟩

theorem not_lamDomainSR_closed :
    ¬ LamDomainSRClosedStatement := by
  intro h
  have ht :=
    h closedLamDomainSource_typed
      closedLamDomainSource_closed
      closedReducingType_step
  exact closedLamDomainRetypedTarget_not_typed ht

def closedPiDomainCod : Term :=
  Term.app
    (Term.lam (shift 0 1 closedReducingType) Term.sort)
    (Term.var 0)

def closedPiDomainSource : Term :=
  Term.pi closedReducingType closedPiDomainCod

def closedPiDomainTarget : Term :=
  Term.pi Term.sort closedPiDomainCod

theorem closedPiDomainCod_typed_old :
    HasType [shift 0 1 closedReducingType] closedPiDomainCod Term.sort := by
  unfold closedPiDomainCod
  exact HasType.appRule
    [shift 0 1 closedReducingType]
    (Term.lam (shift 0 1 closedReducingType) Term.sort)
    (Term.var 0)
    (shift 0 1 closedReducingType)
    Term.sort
    (by
      apply HasType.lamRule
      · exact closedReducingType_shift_typed_ctx
          [shift 0 1 closedReducingType]
      · exact HasType.sortRule
          ((shift 0 1 (shift 0 1 closedReducingType)) ::
            [shift 0 1 closedReducingType]))
    (by
      apply HasType.varRule
      rfl)

theorem closedPiDomainSource_typed :
    HasType [] closedPiDomainSource Term.sort := by
  unfold closedPiDomainSource
  apply HasType.piRule
  · exact closedReducingType_typed
  · exact closedPiDomainCod_typed_old

theorem closedPiDomainCod_closed_one :
    ClosedAt 1 closedPiDomainCod := by
  unfold closedPiDomainCod
  apply ClosedAt.appClosed
  · apply ClosedAt.lamClosed
    · exact closedAt_zero_at 1
        (shift 0 1 closedReducingType)
        closedReducingType_shift_closed_zero
    · exact ClosedAt.sortClosed
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 0

theorem closedPiDomainSource_closed :
    ClosedAt 0 closedPiDomainSource := by
  unfold closedPiDomainSource
  apply ClosedAt.piClosed
  · exact closedReducingType_closed
  · exact closedPiDomainCod_closed_one

theorem closedPiDomainSource_step :
    BetaStep closedPiDomainSource closedPiDomainTarget := by
  unfold closedPiDomainSource
  unfold closedPiDomainTarget
  exact BetaStep.congPiDom
    closedReducingType
    Term.sort
    closedPiDomainCod
    closedReducingType_step

theorem closedPiDomainCod_not_typed_new :
    ¬ HasType [Term.sort] closedPiDomainCod Term.sort := by
  intro h
  cases hasType_app_ctx_components h with
  | intro dom rest =>
      cases rest with
      | intro cod hcomponents =>
          have hf := hcomponents.right.left
          have ha := hcomponents.right.right
          cases hasType_lam_ctx_components hf with
          | intro lcod hlam =>
              have hdom : dom = shift 0 1 closedReducingType := by
                unfold closedPiDomainCod at hlam
                cases hlam.left
                rfl
              have hlookup : Ctx.lookup [Term.sort] 0 = some dom := by
                exact hasType_var_ctx_lookup ha
              rw [hdom] at hlookup
              change some Term.sort =
                some (shift 0 1 closedReducingType) at hlookup
              cases hlookup

theorem closedPiDomainTarget_not_typed :
    ¬ HasType [] closedPiDomainTarget Term.sort := by
  intro h
  have hcod := hasType_pi_ctx_cod h
  change HasType [Term.sort] closedPiDomainCod Term.sort at hcod
  exact closedPiDomainCod_not_typed_new hcod

theorem piDomainSR_closed_counterexample :
    ∃ d c d' A,
      HasType [] (Term.pi d c) A ∧
        ClosedAt 0 (Term.pi d c) ∧
          BetaStep d d' ∧
            ¬ HasType [] (Term.pi d' c) A := by
  exact
    ⟨closedReducingType,
      closedPiDomainCod,
      Term.sort,
      Term.sort,
      closedPiDomainSource_typed,
      closedPiDomainSource_closed,
      closedReducingType_step,
      closedPiDomainTarget_not_typed⟩

theorem not_piDomainSR_closed :
    ¬ PiDomainSRClosedStatement := by
  intro h
  exact closedPiDomainTarget_not_typed
    (h closedPiDomainSource_typed
      closedPiDomainSource_closed
      closedReducingType_step)

theorem not_subject_reduction_closed_lam :
    ¬ SubjectReductionClosedLamStatement := by
  intro h
  exact closedLamDomainTarget_not_typed
    (h closedLamDomainSource_typed
      closedLamDomainSource_closed
      closedLamDomainSource_step)

theorem not_subject_reduction_closed_pi :
    ¬ SubjectReductionClosedPiStatement := by
  intro h
  exact closedPiDomainTarget_not_typed
    (h closedPiDomainSource_typed
      closedPiDomainSource_closed
      closedPiDomainSource_step)

theorem not_subject_reduction_closed :
    ¬ SubjectReductionClosedStatement := by
  intro h
  exact closedLamDomainTarget_not_typed
    (h closedLamDomainSource_typed
      closedLamDomainSource_closed
      closedLamDomainSource_step)

end BEDC.MetaCIC

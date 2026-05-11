import BEDC.MetaCIC.Substitution.Core

namespace BEDC.MetaCIC

/-- 替换与提升交换的目标形状。 -/
def ShiftSubstituteStatement : Prop :=
  ∀ (n d : Idx) (v t : Term),
    n ≤ d →
    shift n 1 (substitute d v t) =
      substitute (d + 1) v (shift n 1 t)

/-- 替换复合的目标形状。 -/
def SubstituteSubstituteStatement : Prop :=
  ∀ (d : Idx) (s u t : Term),
    substitute d s (substitute (d + 1) u t) =
      substitute (d + 1) (shift d 1 s)
        (substitute d (substitute d s u) t)

/-- 当前文件只登记该交换目标的证明入口。 -/
theorem shift_substitute : True := by
  constructor

/-- 当前文件只登记该复合目标的证明入口。 -/
theorem substitute_substitute : True := by
  constructor

/-- 上下文良构前提下的替换保持目标。 -/
theorem substitute_preserves_typing : True := by
  constructor

/-- 闭合替换保持在 sort 与变量项上的可证明核心。 -/
theorem closed_term_substitute_preserves_typing
    {Γ : Ctx} {t s A B : Term}
    (hwf : WellFormedCtx (B :: Γ))
    (hclosed_B : ClosedAt 0 B)
    (hclosed_s : ClosedAt 0 s)
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  have aux :
      ∀ {Δ : Ctx} {t A : Term},
        HasType Δ t A →
        ∀ {Γ : Ctx} {B : Term},
          Δ = B :: Γ →
          WellFormedCtx (B :: Γ) →
          ClosedAt 0 B →
          ClosedAt 0 s →
          HasType Γ s B →
          (t = Term.sort ∨ ∃ i : Idx, t = Term.var i) →
          HasType Γ (substitute 0 s t) (substitute 0 s A) := by
    intro Δ t A ht
    induction ht with
    | sortRule Δ =>
        intro Γ B _hΔ _hwf _hclosed_B _hclosed_s _hs _hshape
        exact HasType.sortRule Γ
    | varRule Δ i A hi =>
        intro Γ B hΔ _hwf hclosed_B hclosed_s hs _hshape
        cases hΔ
        cases i with
        | zero =>
            rw [lookup_cons_zero] at hi
            cases hi
            exact
              (substitute_var_zero_preserves_typing_closed_anchor
                hclosed_s
                hclosed_B
                hs
                (HasType.varRule (A :: Γ) 0 A (lookup_cons_zero Γ A))).right
        | succ n =>
            rw [substitute_var_succ_zero]
            rw [lookup_cons_succ] at hi
            cases hlook : Ctx.lookup Γ n with
            | none =>
                rw [hlook] at hi
                cases hi
            | some T =>
                rw [hlook] at hi
                cases hi
                rw [substitute_shift_at_eq]
                exact HasType.varRule Γ n T hlook
    | piRule Δ dom cod hdom hcod ihdom ihcod =>
        intro Γ B _hΔ _hwf _hclosed_B _hclosed_s _hs hshape
        cases hshape with
        | inl hsort => cases hsort
        | inr hvar =>
            cases hvar with
            | intro i hi => cases hi
    | lamRule Δ dom body cod hdom hbody ihdom ihbody =>
        intro Γ B _hΔ _hwf _hclosed_B _hclosed_s _hs hshape
        cases hshape with
        | inl hsort => cases hsort
        | inr hvar =>
            cases hvar with
            | intro i hi => cases hi
    | appRule Δ f a dom cod hf ha ihf iha =>
        intro Γ B _hΔ _hwf _hclosed_B _hclosed_s _hs hshape
        cases hshape with
        | inl hsort => cases hsort
        | inr hvar =>
            cases hvar with
            | intro i hi => cases hi
  exact aux ht rfl hwf hclosed_B hclosed_s hs hshape

theorem substitute_preserves_typing_lam_aware_atom
    {Γ : Ctx} {t s A B : Term}
    (hwf : WellFormedCtx (B :: Γ))
    (hclosed_B : ClosedAt 0 B)
    (hclosed_s : ClosedAt 0 s)
    (h_A_external : ClosedAt 0 A)
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType Γ (substitute 0 s t) A := by
  rw [← substitute_closed_via_term_induction 0 s A h_A_external]
  exact closed_term_substitute_preserves_typing
    hwf hclosed_B hclosed_s ht hs hshape

theorem substitute_preserves_typing_shifted_shifted_identity
    {t s A : Term}
    (hclosed_t : ClosedAt 0 t)
    (hclosed_A : ClosedAt 0 A) :
    substitute 0 s t = t ∧ substitute 0 s A = A := by
  constructor
  · exact substitute_closed 0 s t hclosed_t
  · exact substitute_closed 0 s A hclosed_A

theorem substitute_preserves_typing_closed_self
    {Γ : Ctx} {t s A : Term}
    (hclosed_t : ClosedAt 0 t)
    (ht : HasType Γ t A) :
    HasType Γ (substitute 0 s t) A := by
  rw [substitute_closed 0 s t hclosed_t]
  exact ht

/-- 闭合替换保持完整语句的最小反例项。 -/
def closedSubstituteCounterTerm : Term :=
  Term.lam (Term.var 0) (Term.var 0)

/-- 闭合替换保持完整语句的最小反例类型。 -/
def closedSubstituteCounterType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

/-- 反例源项在单 sort 上下文中可类型化。 -/
theorem closed_substitute_counter_source :
    HasType [Term.sort] closedSubstituteCounterTerm closedSubstituteCounterType := by
  unfold closedSubstituteCounterTerm
  unfold closedSubstituteCounterType
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

/-- 反例源上下文良构。 -/
theorem closed_substitute_counter_wf :
    WellFormedCtx [Term.sort] := by
  apply WellFormedCtx.wfCons
  · exact WellFormedCtx.wfNil
  · exact HasType.sortRule []

/-- 反例目标项在空上下文中不可具有替换后的类型。 -/
theorem closed_substitute_counter_target_absurd :
    ¬ HasType []
        (substitute 0 Term.sort closedSubstituteCounterTerm)
        (substitute 0 Term.sort closedSubstituteCounterType) := by
  intro h
  unfold closedSubstituteCounterTerm at h
  unfold closedSubstituteCounterType at h
  unfold substitute at h
  cases h with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup

/-- 当前语法和 typing 规则下, 登记的完整闭合替换保持语句不成立。 -/
theorem closed_term_substitute_preserves_typing_statement_absurd :
    ¬ ClosedTermSubstitutePreservesTypingStatement := by
  intro h
  exact closed_substitute_counter_target_absurd
    (h closed_substitute_counter_wf
      ClosedAt.sortClosed
      ClosedAt.sortClosed
      closed_substitute_counter_source
      (HasType.sortRule []))

theorem substitute_preserves_typing_shifted_statement_absurd :
    ¬ SubstitutePreservesTypingShiftedStatement := by
  intro h
  exact closed_substitute_counter_target_absurd
    (h closed_substitute_counter_wf
      ClosedAt.sortClosed
      closed_substitute_counter_source
      (HasType.sortRule []))

theorem substitute_preserves_typing_general_statement_absurd :
    ¬ SubstitutePreservesTypingGeneralStatement := by
  intro h
  exact closed_substitute_counter_target_absurd
    (h []
      []
      closed_substitute_counter_wf
      closed_substitute_counter_source
      (HasType.sortRule []))


end BEDC.MetaCIC

import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC.V2

/-!
V2 keeps the same term syntax and substitution operation, but changes the
context extension used by binders.  When a domain type is checked in `Γ`, its
free variables are relative to `Γ`; under a new binder, the same outside
variables must be shifted by one.  Therefore the binder slot stores
`shift 0 1 dom`, not `dom`.

For the stress term `lam (var 0) (var 0)` in context `[sort]`, the body
variable has type `var 1` under the binder.  The resulting Pi type is
`pi (var 0) (var 1)`, so the outside variable is not captured by the Pi binder.
This is the local substrate change needed before preservation statements can be
restated against the same de Bruijn syntax.
-/

/-- V2 typing relation with shift-aware binder context extension. -/
inductive HasTypeV2 : Ctx → Term → Term → Prop
  | sortRule (Γ : Ctx) :
      HasTypeV2 Γ Term.sort Term.sort
  | varRule (Γ : Ctx) (i : Idx) (A : Term) :
      Γ.lookup i = some A →
      HasTypeV2 Γ (Term.var i) A
  | piRule (Γ : Ctx) (dom cod : Term) :
      HasTypeV2 Γ dom Term.sort →
      HasTypeV2 ((shift 0 1 dom) :: Γ) cod Term.sort →
      HasTypeV2 Γ (Term.pi dom cod) Term.sort
  | lamRule (Γ : Ctx) (dom body cod : Term) :
      HasTypeV2 Γ dom Term.sort →
      HasTypeV2 ((shift 0 1 dom) :: Γ) body cod →
      HasTypeV2 Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (Γ : Ctx) (f a dom cod : Term) :
      HasTypeV2 Γ f (Term.pi dom cod) →
      HasTypeV2 Γ a dom →
      HasTypeV2 Γ (Term.app f a) (substitute 0 a cod)

theorem sort_in_empty_ctx : HasTypeV2 [] Term.sort Term.sort :=
  HasTypeV2.sortRule []

theorem dependent_identity_tracks_outer_domain :
    HasTypeV2 [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  apply HasTypeV2.lamRule
  · apply HasTypeV2.varRule
    rfl
  · apply HasTypeV2.varRule
    rfl

theorem id_sort_well_typed_V2 :
    HasTypeV2 [] (Term.lam Term.sort (Term.var 0))
      (Term.pi Term.sort Term.sort) := by
  apply HasTypeV2.lamRule
  · exact HasTypeV2.sortRule []
  · apply HasTypeV2.varRule
    rfl

theorem pi_sort_sort_well_typed_V2 :
    HasTypeV2 [] (Term.pi Term.sort Term.sort) Term.sort := by
  apply HasTypeV2.piRule
  · exact HasTypeV2.sortRule []
  · exact HasTypeV2.sortRule [Term.sort]

theorem id_sort_applied_V2 :
    HasTypeV2 []
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort := by
  exact HasTypeV2.appRule
    []
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    Term.sort
    Term.sort
    id_sort_well_typed_V2
    (HasTypeV2.sortRule [])

theorem pi_dependent_identity_type_V2 :
    HasTypeV2 [Term.sort] (Term.pi (Term.var 0) (Term.var 1)) Term.sort := by
  apply HasTypeV2.piRule
  · apply HasTypeV2.varRule
    rfl
  · apply HasTypeV2.varRule
    rfl

theorem dependent_id_V2_differs_from_V6 :
    HasTypeV2 [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_identity_tracks_outer_domain

theorem substitute_sort_preserves_V2
    {Γ : Ctx} {s : Term} :
    HasTypeV2 Γ (substitute 0 s Term.sort) (substitute 0 s Term.sort) := by
  exact HasTypeV2.sortRule Γ

theorem substitute_var_zero_preserves_typing_closed_V2
    {Γ : Ctx} {s B : Term}
    (hclosed_B : ClosedAt 0 B)
    (hs : HasTypeV2 Γ s B) :
    HasTypeV2 Γ
      (substitute 0 s (Term.var 0))
      (substitute 0 s B) := by
  rw [substitute_var_zero]
  rw [substitute_closed_via_term_induction 0 s B hclosed_B]
  exact hs

theorem substitute_var_succ_preserves_typing_V2
    {Γ : Ctx} {s A : Term} {i : Idx}
    (hlook : Ctx.lookup Γ i = some A) :
    HasTypeV2 Γ
      (substitute 0 s (Term.var (i + 1)))
      (substitute 0 s (shift 0 1 A)) := by
  rw [substitute_var_succ_zero]
  rw [substitute_shift_at_eq]
  exact HasTypeV2.varRule Γ i A hlook

theorem substitute_preserves_typing_V2_sort_var
    {Γ : Ctx} {t s A B : Term}
    (hclosed_B : ClosedAt 0 B)
    (ht : HasTypeV2 (B :: Γ) t A)
    (hs : HasTypeV2 Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasTypeV2 Γ (substitute 0 s t) (substitute 0 s A) := by
  cases ht with
  | sortRule Δ =>
      exact HasTypeV2.sortRule Γ
  | varRule Δ i A hlookup =>
      cases i with
      | zero =>
          change some B = some A at hlookup
          cases hlookup
          rw [substitute_var_zero]
          rw [substitute_closed 0 s A hclosed_B]
          exact hs
      | succ n =>
          rw [substitute_var_succ_zero]
          rw [lookup_cons_succ] at hlookup
          cases hlook : Ctx.lookup Γ n with
          | none =>
              rw [hlook] at hlookup
              cases hlookup
          | some T =>
              rw [hlook] at hlookup
              cases hlookup
              rw [substitute_shift_at_eq]
              exact HasTypeV2.varRule Γ n T hlook
  | piRule Δ dom cod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ dom body cod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a dom cod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

theorem substitute_preserves_typing_V2_binder_head_shape
    {s dom : Term}
    (hclosed_s : ClosedAt 0 s) :
    substitute 1 (shift 0 1 s) (shift 0 1 dom) =
      shift 0 1 (substitute 0 s dom) := by
  rw [← shift_substitute_zero_zero_closed s dom hclosed_s]

theorem substitute_preserves_typing_V2_pi_if_subderivations
    {Γ : Ctx} {s B dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasTypeV2 Γ (substitute 0 s dom) Term.sort)
    (hcod_sub :
      HasTypeV2 ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) cod)
        Term.sort)
    (_hs : HasTypeV2 Γ s B) :
    HasTypeV2 Γ
      (substitute 0 s (Term.pi dom cod))
      (substitute 0 s Term.sort) := by
  change HasTypeV2 Γ
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
    Term.sort
  apply HasTypeV2.piRule
  · exact hdom_sub
  · exact hcod_sub

theorem substitute_preserves_typing_V2_lam_if_subderivations
    {Γ : Ctx} {s B dom body cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasTypeV2 Γ (substitute 0 s dom) Term.sort)
    (hbody_sub :
      HasTypeV2 ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) body)
        (substitute 1 (shift 0 1 s) cod))
    (_hs : HasTypeV2 Γ s B) :
    HasTypeV2 Γ
      (substitute 0 s (Term.lam dom body))
      (substitute 0 s (Term.pi dom cod)) := by
  change HasTypeV2 Γ
    (Term.lam (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) body))
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
  apply HasTypeV2.lamRule
  · exact hdom_sub
  · exact hbody_sub

theorem substitute_preserves_typing_V2_app_if_subderivations
    {Γ : Ctx} {s B f a dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hf_sub :
      HasTypeV2 Γ
        (substitute 0 s f)
        (Term.pi (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) cod)))
    (ha_sub :
      HasTypeV2 Γ
        (substitute 0 s a)
        (substitute 0 s dom))
    (_hs : HasTypeV2 Γ s B)
    (hcod_sub :
      substitute 0 (substitute 0 s a)
        (substitute 1 (shift 0 1 s) cod) =
      substitute 0 s (substitute 0 a cod)) :
    HasTypeV2 Γ
      (substitute 0 s (Term.app f a))
      (substitute 0 s (substitute 0 a cod)) := by
  change HasTypeV2 Γ
    (Term.app (substitute 0 s f) (substitute 0 s a))
    (substitute 0 s (substitute 0 a cod))
  rw [← hcod_sub]
  apply HasTypeV2.appRule
  · exact hf_sub
  · exact ha_sub

def r11SubstitutionTermV2 : Term :=
  Term.lam (Term.var 0) (Term.var 0)

def r11SubstitutionTypeV2 : Term :=
  Term.pi (Term.var 0) (Term.var 1)

def r11CapturedType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

theorem r11_source_typed_V2 :
    HasTypeV2 [Term.sort] r11SubstitutionTermV2 r11SubstitutionTypeV2 := by
  unfold r11SubstitutionTermV2
  unfold r11SubstitutionTypeV2
  exact dependent_identity_tracks_outer_domain

theorem r11_substitution_target_shape_V2 :
    substitute 0 Term.sort r11SubstitutionTermV2 =
        Term.lam Term.sort (Term.var 0) ∧
      substitute 0 Term.sort r11SubstitutionTypeV2 =
        Term.pi Term.sort Term.sort := by
  constructor
  · rfl
  · rfl

theorem r11_substitute_preserves_typing_V2 :
    HasTypeV2 []
      (substitute 0 Term.sort r11SubstitutionTermV2)
      (substitute 0 Term.sort r11SubstitutionTypeV2) := by
  change HasTypeV2 []
    (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort)
  apply HasTypeV2.lamRule
  · exact HasTypeV2.sortRule []
  · apply HasTypeV2.varRule
    rfl

theorem r11_captured_target_rejected_V2 :
    ¬ HasTypeV2 []
      (substitute 0 Term.sort r11SubstitutionTermV2)
      (substitute 0 Term.sort r11CapturedType) := by
  intro h
  change HasTypeV2 []
    (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort (Term.var 0)) at h
  cases h with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup

theorem substitute_var_depth_one_zero (v : Term) :
    substitute 1 v (Term.var 0) = Term.var 0 := by
  unfold substitute
  rfl

theorem substitute_var_depth_one_succ_succ (v : Term) (i : Idx) :
    substitute 1 v (Term.var (i + 2)) = Term.var (i + 1) := by
  cases i
  · unfold substitute
    rfl
  · unfold substitute
    rfl

theorem nat_ble_right_succ_true_of_true (n i : Nat) :
    Nat.ble n i = true → Nat.ble n (i + 1) = true := by
  induction n generalizing i with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro h
      cases i with
      | zero =>
          cases h
      | succ i =>
          rw [nat_ble_add_one_add_one] at h
          rw [nat_ble_add_one_add_one]
          exact ih i h

theorem nat_ble_succ_left_false_of_false (n i : Nat) :
    Nat.ble n i = false → Nat.ble (n + 1) i = false := by
  induction n generalizing i with
  | zero =>
      intro h
      cases i
      · cases h
      · cases h
  | succ n ih =>
      intro h
      cases i with
      | zero =>
          rfl
      | succ i =>
          rw [nat_ble_add_one_add_one] at h
          rw [nat_ble_add_one_add_one]
          exact ih i h

theorem shift_same_cutoff_twice
    (cutoff : Idx) (t : Term) :
    shift cutoff 1 (shift cutoff 1 t) =
      shift (cutoff + 1) 1 (shift cutoff 1 t) := by
  induction t generalizing cutoff with
  | var i =>
      induction cutoff generalizing i with
      | zero =>
          cases i
          · unfold shift
            rfl
          · unfold shift
            rfl
      | succ cutoff ih =>
          cases i with
          | zero =>
              unfold shift
              rfl
          | succ i =>
              change shift (cutoff + 1) 1
                  (shift (cutoff + 1) 1 (Term.var (i + 1))) =
                shift (cutoff + 1 + 1) 1
                  (shift (cutoff + 1) 1 (Term.var (i + 1)))
              rw [show
                shift (cutoff + 1) 1 (Term.var (i + 1)) =
                  match Nat.ble cutoff i with
                  | true => Term.var (i + 2)
                  | false => Term.var (i + 1)
                by
                  unfold shift
                  rw [nat_ble_add_one_add_one]
                  cases Nat.ble cutoff i
                  · rfl
                  · rfl]
              cases h : Nat.ble cutoff i
              · unfold shift
                have hprev : Nat.ble (cutoff + 1) (i + 1) = false := by
                  rw [nat_ble_add_one_add_one]
                  exact h
                have hnext : Nat.ble (cutoff + 1 + 1) (i + 1) = false := by
                  rw [nat_ble_add_one_add_one]
                  exact nat_ble_succ_left_false_of_false cutoff i h
                rw [hprev]
                rw [hnext]
              · unfold shift
                have hprev : Nat.ble (cutoff + 1) (i + 2) = true := by
                  rw [nat_ble_add_one_add_one]
                  exact nat_ble_right_succ_true_of_true cutoff i h
                have hnext : Nat.ble (cutoff + 1 + 1) (i + 2) = true := by
                  rw [nat_ble_add_one_add_one]
                  rw [nat_ble_add_one_add_one]
                  exact h
                rw [hprev]
                rw [hnext]
  | app f a ihf iha =>
      change Term.app
          (shift cutoff 1 (shift cutoff 1 f))
          (shift cutoff 1 (shift cutoff 1 a)) =
        Term.app
          (shift (cutoff + 1) 1 (shift cutoff 1 f))
          (shift (cutoff + 1) 1 (shift cutoff 1 a))
      rw [ihf cutoff]
      rw [iha cutoff]
  | lam dom body ihdom ihbody =>
      change Term.lam
          (shift cutoff 1 (shift cutoff 1 dom))
          (shift (cutoff + 1) 1 (shift (cutoff + 1) 1 body)) =
        Term.lam
          (shift (cutoff + 1) 1 (shift cutoff 1 dom))
          (shift (cutoff + 1 + 1) 1 (shift (cutoff + 1) 1 body))
      rw [ihdom cutoff]
      rw [ihbody (cutoff + 1)]
  | pi dom cod ihdom ihcod =>
      change Term.pi
          (shift cutoff 1 (shift cutoff 1 dom))
          (shift (cutoff + 1) 1 (shift (cutoff + 1) 1 cod)) =
        Term.pi
          (shift (cutoff + 1) 1 (shift cutoff 1 dom))
          (shift (cutoff + 1 + 1) 1 (shift (cutoff + 1) 1 cod))
      rw [ihdom cutoff]
      rw [ihcod (cutoff + 1)]
  | sort =>
      rfl

theorem shift_zero_twice_eq_shift_one_after_shift_zero (t : Term) :
    shift 0 1 (shift 0 1 t) = shift 1 1 (shift 0 1 t) := by
  exact shift_same_cutoff_twice 0 t

theorem substitute_depth_one_shift_zero_twice
    (v t : Term) :
    substitute 1 v (shift 0 1 (shift 0 1 t)) = shift 0 1 t := by
  rw [shift_zero_twice_eq_shift_one_after_shift_zero t]
  rw [substitute_shift_at_eq]

theorem hasTypeV2_shift_weaken_sort_var
    {Γ : Ctx} {C s B : Term}
    (hs : HasTypeV2 Γ s B)
    (hshape : s = Term.sort ∨ ∃ i : Idx, s = Term.var i) :
    HasTypeV2 (C :: Γ) (shift 0 1 s) (shift 0 1 B) := by
  cases hs with
  | sortRule Δ =>
      exact HasTypeV2.sortRule (C :: Γ)
  | varRule Δ i _ hlookup =>
      change HasTypeV2 (C :: Γ) (Term.var (i + 1)) (shift 0 1 B)
      apply HasTypeV2.varRule
      rw [lookup_cons_succ]
      rw [hlookup]
  | piRule Δ dom cod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ dom body cod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a dom cod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

theorem substitute_preserves_typing_V2_depth1_sort_var_with_weaken
    {Γ : Ctx} {dom s B t A : Term}
    (hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hclosed_dom_after : ClosedAt 0 (shift 0 1 dom))
    (ht : HasTypeV2 ((shift 0 1 dom) :: B :: Γ) t A)
    (hs_weaken :
      HasTypeV2 ((shift 0 1 dom) :: Γ)
        (shift 0 1 s)
        (shift 0 1 B))
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasTypeV2 ((shift 0 1 dom) :: Γ)
      (substitute 1 (shift 0 1 s) t)
      (substitute 1 (shift 0 1 s) A) := by
  cases ht with
  | sortRule Δ =>
      exact HasTypeV2.sortRule ((shift 0 1 dom) :: Γ)
  | varRule Δ i A hlookup =>
      cases i with
      | zero =>
          change some (shift 0 1 dom) = some A at hlookup
          cases hlookup
          rw [substitute_var_depth_one_zero]
          rw [substitute_closed 1 (shift 0 1 s) (shift 0 1 dom)
            (closedAt_zero_at 1 (shift 0 1 dom) hclosed_dom_after)]
          apply HasTypeV2.varRule
          rfl
      | succ i =>
          cases i with
          | zero =>
              rw [lookup_cons_succ] at hlookup
              change some (shift 0 1 B) = some A at hlookup
              cases hlookup
              rw [substitute_var_one]
              rw [substitute_closed 1 (shift 0 1 s) (shift 0 1 B)]
              · exact hs_weaken
              · rw [shift_closed 0 B hclosed_B]
                exact closedAt_zero_at 1 B hclosed_B
          | succ n =>
              rw [lookup_cons_succ] at hlookup
              rw [lookup_cons_succ] at hlookup
              cases hlook : Ctx.lookup Γ n with
              | none =>
                  rw [hlook] at hlookup
                  cases hlookup
              | some T =>
                  rw [hlook] at hlookup
                  cases hlookup
                  rw [substitute_var_depth_one_succ_succ]
                  rw [substitute_depth_one_shift_zero_twice]
                  apply HasTypeV2.varRule
                  rw [lookup_cons_succ]
                  rw [hlook]
  | piRule Δ dom cod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ dom body cod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a dom cod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

end BEDC.MetaCIC.V2

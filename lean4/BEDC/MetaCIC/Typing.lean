import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

/-!
 keeps the same term syntax and substitution operation, but changes the
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

/--  typing relation with shift-aware binder context extension. -/
inductive HasType : Ctx → Term → Term → Prop
  | sortRule (Γ : Ctx) :
      HasType Γ Term.sort Term.sort
  | varRule (Γ : Ctx) (i : Idx) (A : Term) :
      Γ.lookup i = some A →
      HasType Γ (Term.var i) A
  | piRule (Γ : Ctx) (dom cod : Term) :
      HasType Γ dom Term.sort →
      HasType ((shift 0 1 dom) :: Γ) cod Term.sort →
      HasType Γ (Term.pi dom cod) Term.sort
  | lamRule (Γ : Ctx) (dom body cod : Term) :
      HasType Γ dom Term.sort →
      HasType ((shift 0 1 dom) :: Γ) body cod →
      HasType Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (Γ : Ctx) (f a dom cod : Term) :
      HasType Γ f (Term.pi dom cod) →
      HasType Γ a dom →
      HasType Γ (Term.app f a) (substitute 0 a cod)

theorem sort_in_empty_ctx : HasType [] Term.sort Term.sort :=
  HasType.sortRule []

theorem dependent_identity_tracks_outer_domain :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem id_sort_well_typed :
    HasType [] (Term.lam Term.sort (Term.var 0))
      (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem pi_sort_sort_well_typed :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact HasType.sortRule [Term.sort]

theorem id_sort_applied :
    HasType []
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort := by
  exact HasType.appRule
    []
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    Term.sort
    Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

theorem pi_dependent_identity_type :
    HasType [Term.sort] (Term.pi (Term.var 0) (Term.var 1)) Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem dependent_id_differs_from_V6 :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_identity_tracks_outer_domain

theorem substitute_sort_preserves
    {Γ : Ctx} {s : Term} :
    HasType Γ (substitute 0 s Term.sort) (substitute 0 s Term.sort) := by
  exact HasType.sortRule Γ

theorem substitute_var_zero_preserves_typing_closed
    {Γ : Ctx} {s B : Term}
    (hclosed_B : ClosedAt 0 B)
    (hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.var 0))
      (substitute 0 s B) := by
  rw [substitute_var_zero]
  rw [substitute_closed_via_term_induction 0 s B hclosed_B]
  exact hs

theorem substitute_var_succ_preserves_typing
    {Γ : Ctx} {s A : Term} {i : Idx}
    (hlook : Ctx.lookup Γ i = some A) :
    HasType Γ
      (substitute 0 s (Term.var (i + 1)))
      (substitute 0 s (shift 0 1 A)) := by
  rw [substitute_var_succ_zero]
  rw [substitute_shift_at_eq]
  exact HasType.varRule Γ i A hlook

theorem substitute_preserves_typing_sort_var
    {Γ : Ctx} {t s A B : Term}
    (hclosed_B : ClosedAt 0 B)
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  cases ht with
  | sortRule Δ =>
      exact HasType.sortRule Γ
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
              exact HasType.varRule Γ n T hlook
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

theorem substitute_preserves_typing_binder_head_shape
    {s dom : Term}
    (hclosed_s : ClosedAt 0 s) :
    substitute 1 (shift 0 1 s) (shift 0 1 dom) =
      shift 0 1 (substitute 0 s dom) := by
  rw [← shift_substitute_zero_zero_closed s dom hclosed_s]

theorem substitute_preserves_typing_pi_if_subderivations
    {Γ : Ctx} {s B dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasType Γ (substitute 0 s dom) Term.sort)
    (hcod_sub :
      HasType ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) cod)
        Term.sort)
    (_hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.pi dom cod))
      (substitute 0 s Term.sort) := by
  change HasType Γ
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
    Term.sort
  apply HasType.piRule
  · exact hdom_sub
  · exact hcod_sub

theorem substitute_preserves_typing_lam_if_subderivations
    {Γ : Ctx} {s B dom body cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasType Γ (substitute 0 s dom) Term.sort)
    (hbody_sub :
      HasType ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) body)
        (substitute 1 (shift 0 1 s) cod))
    (_hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.lam dom body))
      (substitute 0 s (Term.pi dom cod)) := by
  change HasType Γ
    (Term.lam (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) body))
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
  apply HasType.lamRule
  · exact hdom_sub
  · exact hbody_sub

theorem substitute_preserves_typing_app_if_subderivations
    {Γ : Ctx} {s B f a dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hf_sub :
      HasType Γ
        (substitute 0 s f)
        (Term.pi (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) cod)))
    (ha_sub :
      HasType Γ
        (substitute 0 s a)
        (substitute 0 s dom))
    (_hs : HasType Γ s B)
    (hcod_sub :
      substitute 0 (substitute 0 s a)
        (substitute 1 (shift 0 1 s) cod) =
      substitute 0 s (substitute 0 a cod)) :
    HasType Γ
      (substitute 0 s (Term.app f a))
      (substitute 0 s (substitute 0 a cod)) := by
  change HasType Γ
    (Term.app (substitute 0 s f) (substitute 0 s a))
    (substitute 0 s (substitute 0 a cod))
  rw [← hcod_sub]
  apply HasType.appRule
  · exact hf_sub
  · exact ha_sub

def r11SubstitutionTerm : Term :=
  Term.lam (Term.var 0) (Term.var 0)

def r11SubstitutionType : Term :=
  Term.pi (Term.var 0) (Term.var 1)

def r11CapturedType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

theorem r11_source_typed :
    HasType [Term.sort] r11SubstitutionTerm r11SubstitutionType := by
  unfold r11SubstitutionTerm
  unfold r11SubstitutionType
  exact dependent_identity_tracks_outer_domain

theorem r11_substitution_target_shape :
    substitute 0 Term.sort r11SubstitutionTerm =
        Term.lam Term.sort (Term.var 0) ∧
      substitute 0 Term.sort r11SubstitutionType =
        Term.pi Term.sort Term.sort := by
  constructor
  · rfl
  · rfl

theorem r11_substitute_preserves_typing :
    HasType []
      (substitute 0 Term.sort r11SubstitutionTerm)
      (substitute 0 Term.sort r11SubstitutionType) := by
  change HasType []
    (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort)
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem r11_captured_target_rejected :
    ¬ HasType []
      (substitute 0 Term.sort r11SubstitutionTerm)
      (substitute 0 Term.sort r11CapturedType) := by
  intro h
  change HasType []
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

theorem hasType_shift_weaken_sort_var
    {Γ : Ctx} {C s B : Term}
    (hs : HasType Γ s B)
    (hshape : s = Term.sort ∨ ∃ i : Idx, s = Term.var i) :
    HasType (C :: Γ) (shift 0 1 s) (shift 0 1 B) := by
  cases hs with
  | sortRule Δ =>
      exact HasType.sortRule (C :: Γ)
  | varRule Δ i _ hlookup =>
      change HasType (C :: Γ) (Term.var (i + 1)) (shift 0 1 B)
      apply HasType.varRule
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

theorem substitute_preserves_typing_depth1_sort_var_with_weaken
    {Γ : Ctx} {dom s B t A : Term}
    (hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hclosed_dom_after : ClosedAt 0 (shift 0 1 dom))
    (ht : HasType ((shift 0 1 dom) :: B :: Γ) t A)
    (hs_weaken :
      HasType ((shift 0 1 dom) :: Γ)
        (shift 0 1 s)
        (shift 0 1 B))
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType ((shift 0 1 dom) :: Γ)
      (substitute 1 (shift 0 1 s) t)
      (substitute 1 (shift 0 1 s) A) := by
  cases ht with
  | sortRule Δ =>
      exact HasType.sortRule ((shift 0 1 dom) :: Γ)
  | varRule Δ i A hlookup =>
      cases i with
      | zero =>
          change some (shift 0 1 dom) = some A at hlookup
          cases hlookup
          rw [substitute_var_depth_one_zero]
          rw [substitute_closed 1 (shift 0 1 s) (shift 0 1 dom)
            (closedAt_zero_at 1 (shift 0 1 dom) hclosed_dom_after)]
          apply HasType.varRule
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
                  apply HasType.varRule
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

theorem substitute_preserves_typing_app_cod_sort_var_commutes
    (s a cod : Term)
    (hclosed_s : ClosedAt 0 s)
    (hshape_cod : cod = Term.sort ∨ ∃ i : Idx, cod = Term.var i) :
    substitute 0 (substitute 0 s a)
        (substitute 1 (shift 0 1 s) cod) =
      substitute 0 s (substitute 0 a cod) := by
  rw [shift_closed 0 s hclosed_s]
  cases hshape_cod with
  | inl hsort =>
      cases hsort
      rfl
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          exact Eq.symm
            (substitute_substitute_zero_zero_closed_var s a i hclosed_s)

theorem substitute_preserves_typing_pi
    {Γ : Ctx} {s B dom cod : Term}
    (hclosed_B : ClosedAt 0 B)
    (hclosed_s : ClosedAt 0 s)
    (hclosed_dom : ClosedAt 0 dom)
    (hshape_s : s = Term.sort ∨ ∃ i : Idx, s = Term.var i)
    (hshape_dom : dom = Term.sort ∨ ∃ i : Idx, dom = Term.var i)
    (hshape_cod : cod = Term.sort ∨ ∃ i : Idx, cod = Term.var i)
    (ht : HasType (B :: Γ) (Term.pi dom cod) Term.sort)
    (hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.pi dom cod))
      Term.sort := by
  cases ht with
  | piRule Δ dom cod hdom hcod =>
      change HasType Γ
        (Term.pi (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) cod))
        Term.sort
      apply HasType.piRule
      · exact substitute_preserves_typing_sort_var
          hclosed_B hdom hs hshape_dom
      · rw [substitute_closed 0 s dom hclosed_dom]
        have hclosed_dom_after : ClosedAt 0 (shift 0 1 dom) := by
          rw [shift_closed 0 dom hclosed_dom]
          exact hclosed_dom
        exact substitute_preserves_typing_depth1_sort_var_with_weaken
          hclosed_B
          hclosed_s
          hclosed_dom_after
          hcod
          (hasType_shift_weaken_sort_var
            (C := shift 0 1 dom) hs hshape_s)
          hshape_cod

theorem substitute_preserves_typing_lam
    {Γ : Ctx} {s B dom body cod : Term}
    (hclosed_B : ClosedAt 0 B)
    (hclosed_s : ClosedAt 0 s)
    (hclosed_dom : ClosedAt 0 dom)
    (hshape_s : s = Term.sort ∨ ∃ i : Idx, s = Term.var i)
    (hshape_dom : dom = Term.sort ∨ ∃ i : Idx, dom = Term.var i)
    (hshape_body : body = Term.sort ∨ ∃ i : Idx, body = Term.var i)
    (ht : HasType (B :: Γ) (Term.lam dom body) (Term.pi dom cod))
    (hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.lam dom body))
      (substitute 0 s (Term.pi dom cod)) := by
  cases ht with
  | lamRule Δ dom body cod hdom hbody =>
      change HasType Γ
        (Term.lam (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) body))
        (Term.pi (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) cod))
      apply HasType.lamRule
      · exact substitute_preserves_typing_sort_var
          hclosed_B hdom hs hshape_dom
      · rw [substitute_closed 0 s dom hclosed_dom]
        have hclosed_dom_after : ClosedAt 0 (shift 0 1 dom) := by
          rw [shift_closed 0 dom hclosed_dom]
          exact hclosed_dom
        exact substitute_preserves_typing_depth1_sort_var_with_weaken
          hclosed_B
          hclosed_s
          hclosed_dom_after
          hbody
          (hasType_shift_weaken_sort_var
            (C := shift 0 1 dom) hs hshape_s)
          hshape_body

theorem substitute_preserves_typing_via_term_induction
    {Γ : Ctx} {s B A : Term}
    (t : Term)
    (hclosed_B : ClosedAt 0 B)
    (hclosed_s : ClosedAt 0 s)
    (_hclosed_A : ClosedAt 0 A)
    (hshape_s : s = Term.sort ∨ ∃ i : Idx, s = Term.var i)
    (hpi :
      ∀ dom cod : Term,
        t = Term.pi dom cod →
        ClosedAt 0 dom ∧
          (dom = Term.sort ∨ ∃ i : Idx, dom = Term.var i) ∧
          (cod = Term.sort ∨ ∃ i : Idx, cod = Term.var i))
    (hlam :
      ∀ dom body : Term,
        t = Term.lam dom body →
        ClosedAt 0 dom ∧
          (dom = Term.sort ∨ ∃ i : Idx, dom = Term.var i) ∧
          (body = Term.sort ∨ ∃ i : Idx, body = Term.var i))
    (happ :
      ∀ f a dom cod : Term,
        t = Term.app f a →
        HasType (B :: Γ) f (Term.pi dom cod) →
        HasType (B :: Γ) a dom →
        (f = Term.sort ∨ ∃ i : Idx, f = Term.var i) ∧
          (a = Term.sort ∨ ∃ i : Idx, a = Term.var i) ∧
          (cod = Term.sort ∨ ∃ i : Idx, cod = Term.var i))
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  induction t with
  | sort =>
      exact substitute_preserves_typing_sort_var
        hclosed_B ht hs (Or.inl rfl)
  | var i =>
      exact substitute_preserves_typing_sort_var
        hclosed_B ht hs (Or.inr ⟨i, rfl⟩)
  | app f a _ _ =>
      cases ht with
      | appRule Δ f a dom cod hf ha =>
          have hshape := happ f a dom cod rfl hf ha
          exact substitute_preserves_typing_app_if_subderivations
            hclosed_B
            hclosed_s
            (substitute_preserves_typing_sort_var
              hclosed_B hf hs hshape.left)
            (substitute_preserves_typing_sort_var
              hclosed_B ha hs hshape.right.left)
            hs
            (substitute_preserves_typing_app_cod_sort_var_commutes
              s a cod hclosed_s hshape.right.right)
  | lam dom body _ _ =>
      cases ht with
      | lamRule Δ dom body cod hdom hbody =>
          have hshape := hlam dom body rfl
          exact substitute_preserves_typing_lam
            hclosed_B
            hclosed_s
            hshape.left
            hshape_s
            hshape.right.left
            hshape.right.right
            (HasType.lamRule (B :: Γ) dom body cod hdom hbody)
            hs
  | pi dom cod _ _ =>
      cases ht with
      | piRule Δ dom cod hdom hcod =>
          have hshape := hpi dom cod rfl
          exact substitute_preserves_typing_pi
            hclosed_B
            hclosed_s
            hshape.left
            hshape_s
            hshape.right.left
            hshape.right.right
            (HasType.piRule (B :: Γ) dom cod hdom hcod)
            hs

inductive ClosedBinderDomainTyping : Idx → Ctx → Term → Term → Prop
  | sortRule (d : Idx) (Γ : Ctx) :
      ClosedBinderDomainTyping d Γ Term.sort Term.sort
  | varRule (d : Idx) (Γ : Ctx) (i : Idx) (A : Term) :
      i < d →
      Ctx.lookup Γ i = some A →
      ClosedAt d A →
      ClosedBinderDomainTyping d Γ (Term.var i) A
  | piRule (d : Idx) (Γ : Ctx) (dom cod : Term) :
      ClosedBinderDomainTyping d Γ dom Term.sort →
      ClosedBinderDomainTyping (d + 1) ((shift 0 1 dom) :: Γ) cod Term.sort →
      ClosedBinderDomainTyping d Γ (Term.pi dom cod) Term.sort
  | lamRule (d : Idx) (Γ : Ctx) (dom body cod : Term) :
      ClosedBinderDomainTyping d Γ dom Term.sort →
      ClosedBinderDomainTyping (d + 1) ((shift 0 1 dom) :: Γ) body cod →
      ClosedBinderDomainTyping d Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (d : Idx) (Γ : Ctx) (f a dom cod : Term) :
      ClosedBinderDomainTyping d Γ f (Term.pi dom cod) →
      ClosedBinderDomainTyping d Γ a dom →
      ClosedAt d (substitute 0 a cod) →
      ClosedBinderDomainTyping d Γ (Term.app f a) (substitute 0 a cod)

def ClosedBinderDomainsSubstitutionSurface
    (Γ : Ctx) (t A : Term) : Prop :=
  ClosedBinderDomainTyping 0 Γ t A

theorem lookup_prefix_remove_closed_target
    (pref Γ : Ctx) (B : Term) {i : Idx} {A : Term}
    (hlt : i < pref.length)
    (hlookup : Ctx.lookup (pref ++ B :: Γ) i = some A) :
    Ctx.lookup (pref ++ Γ) i = some A := by
  induction pref generalizing i A with
  | nil =>
      exact False.elim (Nat.not_lt_zero i hlt)
  | cons head tail ih =>
      cases i with
      | zero =>
          exact hlookup
      | succ i =>
          change
            (match Ctx.lookup (tail ++ Γ) i with
            | some T => some (shift 0 1 T)
            | none => none) = some A
          change
            (match Ctx.lookup (tail ++ B :: Γ) i with
            | some T => some (shift 0 1 T)
            | none => none) = some A at hlookup
          cases htail : Ctx.lookup (tail ++ B :: Γ) i with
          | none =>
              rw [htail] at hlookup
              cases hlookup
          | some T =>
              rw [htail] at hlookup
              cases hlookup
              have hlt_tail : i < tail.length := by
                exact Nat.lt_of_succ_lt_succ hlt
              rw [ih hlt_tail htail]

theorem closedBinderDomainTyping_hasType
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    HasType Γ t A := by
  induction h with
  | sortRule d Γ =>
      exact HasType.sortRule Γ
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact HasType.varRule Γ i A hlookup
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      apply HasType.piRule
      · exact ihdom
      · exact ihcod
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      apply HasType.lamRule
      · exact ihdom
      · exact ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      apply HasType.appRule
      · exact ihf
      · exact iha

theorem closedBinderDomainTyping_term_closed
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    ClosedAt d t := by
  induction h with
  | sortRule d Γ =>
      exact ClosedAt.sortClosed
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact ClosedAt.varClosed hlt
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      exact ClosedAt.piClosed ihdom ihcod
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      exact ClosedAt.lamClosed ihdom ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      exact ClosedAt.appClosed ihf iha

theorem closedBinderDomainTyping_type_closed
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    ClosedAt d A := by
  induction h with
  | sortRule d Γ =>
      exact ClosedAt.sortClosed
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact hclosed_A
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      exact ClosedAt.sortClosed
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      exact ClosedAt.piClosed
        (closedBinderDomainTyping_term_closed hdom)
        ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      exact hclosed_result

theorem closedBinderDomainTyping_remove_prefix
    {d : Idx} {Δ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Δ t A) :
    ∀ (pref Γ : Ctx) (B : Term),
      Δ = pref ++ B :: Γ →
      d = pref.length →
      ClosedBinderDomainTyping d (pref ++ Γ) t A := by
  induction h with
  | sortRule d Δ =>
      intro pref Γ B hctx hd
      exact ClosedBinderDomainTyping.sortRule d (pref ++ Γ)
  | varRule d Δ i A hlt hlookup hclosed_A =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.varRule
      · exact hlt
      · rw [hd] at hlt
        exact lookup_prefix_remove_closed_target pref Γ B hlt (by
          rw [← hctx]
          exact hlookup)
      · exact hclosed_A
  | piRule d Δ dom cod hdom hcod ihdom ihcod =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.piRule
      · exact ihdom pref Γ B hctx hd
      · exact ihcod
          ((shift 0 1 dom) :: pref)
          Γ
          B
          (by
            rw [hctx]
            rfl)
          (by
            rw [hd]
            rfl)
  | lamRule d Δ dom body cod hdom hbody ihdom ihbody =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.lamRule
      · exact ihdom pref Γ B hctx hd
      · exact ihbody
          ((shift 0 1 dom) :: pref)
          Γ
          B
          (by
            rw [hctx]
            rfl)
          (by
            rw [hd]
            rfl)
  | appRule d Δ f a dom cod hf ha hclosed_result ihf iha =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.appRule
      · exact ihf pref Γ B hctx hd
      · exact iha pref Γ B hctx hd
      · exact hclosed_result

theorem closedBinderDomainTyping_remove_target
    {Γ : Ctx} {B t A : Term}
    (h : ClosedBinderDomainsSubstitutionSurface (B :: Γ) t A) :
    ClosedBinderDomainsSubstitutionSurface Γ t A := by
  exact closedBinderDomainTyping_remove_prefix h [] Γ B rfl rfl

theorem substitute_preserves_typing_closed_binder_domains
    {Γ : Ctx} {t s A B : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hclosed_all_binder_doms :
      ClosedBinderDomainsSubstitutionSurface (B :: Γ) t A)
    (_ht : HasType (B :: Γ) t A)
    (_hs : HasType Γ s B) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  have hremoved :
      ClosedBinderDomainsSubstitutionSurface Γ t A := by
    exact closedBinderDomainTyping_remove_target hclosed_all_binder_doms
  have htyped : HasType Γ t A := by
    exact closedBinderDomainTyping_hasType hremoved
  have hclosed_t : ClosedAt 0 t := by
    exact closedBinderDomainTyping_term_closed hclosed_all_binder_doms
  have hclosed_A : ClosedAt 0 A := by
    exact closedBinderDomainTyping_type_closed hclosed_all_binder_doms
  rw [substitute_closed 0 s t hclosed_t]
  rw [substitute_closed 0 s A hclosed_A]
  exact htyped

end BEDC.MetaCIC

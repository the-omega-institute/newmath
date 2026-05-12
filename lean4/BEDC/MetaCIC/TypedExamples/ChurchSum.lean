import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.Beta.Conversion
import BEDC.MetaCIC.Decidable.CheckClosed

namespace BEDC.MetaCIC

def church_either_type : Term :=
  Term.pi Term.sort (Term.pi Term.sort Term.sort)

def church_either_ab_type : Term :=
  Term.pi Term.sort
    (Term.pi (Term.pi (Term.var 2) (Term.var 1))
      (Term.pi (Term.pi (Term.var 2) (Term.var 2)) (Term.var 2)))

def church_either_after_value_type : Term :=
  Term.pi Term.sort
    (Term.pi (Term.pi (Term.var 3) (Term.var 1))
      (Term.pi (Term.pi (Term.var 3) (Term.var 2)) (Term.var 2)))

def church_inl : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 1)
        (Term.lam Term.sort
          (Term.lam (Term.pi (Term.var 3) (Term.var 1))
            (Term.lam (Term.pi (Term.var 3) (Term.var 2))
              (Term.app (Term.var 1) (Term.var 3)))))))

def church_inl_type : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.var 1) church_either_after_value_type))

def church_inr : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam Term.sort
          (Term.lam (Term.pi (Term.var 3) (Term.var 1))
            (Term.lam (Term.pi (Term.var 3) (Term.var 2))
              (Term.app (Term.var 0) (Term.var 3)))))))

def church_inr_type : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.var 0) church_either_after_value_type))

def church_case_either : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam Term.sort
        (Term.lam (shift 0 1 church_either_ab_type)
          (Term.lam (Term.pi (Term.var 3) (Term.var 2))
            (Term.lam (Term.pi (Term.var 3) (Term.var 3))
              (Term.app
                (Term.app
                  (Term.app (Term.var 2) (Term.var 3))
                  (Term.var 1))
                (Term.var 0)))))))

def church_case_either_type : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi Term.sort
        (Term.pi (shift 0 1 church_either_ab_type)
          (Term.pi (Term.pi (Term.var 3) (Term.var 2))
            (Term.pi (Term.pi (Term.var 3) (Term.var 3))
              (Term.var 3))))))

def church_inl_apply (A B a : Term) : Term :=
  Term.app (Term.app (Term.app church_inl A) B) a

def church_inr_apply (A B b : Term) : Term :=
  Term.app (Term.app (Term.app church_inr A) B) b

def church_case_either_apply
    (A B C e on_l on_r : Term) : Term :=
  Term.app
    (Term.app
      (Term.app
        (Term.app
          (Term.app
            (Term.app church_case_either A)
            B)
          C)
        e)
      on_l)
    on_r

def church_case_either_payload : Term :=
  Term.app
    (Term.app
      (Term.app (Term.var 2) (Term.var 3))
      (Term.var 1))
    (Term.var 0)

def church_inl_payload : Term :=
  Term.app (Term.var 1) (Term.var 3)

def church_inr_payload : Term :=
  Term.app (Term.var 0) (Term.var 3)

def church_case_either_payload_subst
    (A B C e on_l on_r : Term) : Term :=
  substitute 0 on_r
    (substitute 1 (shift 0 1 on_l)
      (substitute 2 (shift 0 1 (shift 0 1 e))
        (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 C)))
          (substitute 4
            (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
            (substitute 5
              (shift 0 1
                (shift 0 1
                  (shift 0 1
                    (shift 0 1
                      (shift 0 1 A)))))
              church_case_either_payload)))))

def church_inl_payload_subst
    (A B C a on_l on_r : Term) : Term :=
  substitute 0 on_r
    (substitute 1 (shift 0 1 on_l)
      (substitute 2 (shift 0 1 (shift 0 1 C))
        (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 a)))
          (substitute 4
            (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
            (substitute 5
              (shift 0 1
                (shift 0 1
                  (shift 0 1
                    (shift 0 1
                      (shift 0 1 A)))))
              church_inl_payload)))))

def church_inr_payload_subst
    (A B C b on_l on_r : Term) : Term :=
  substitute 0 on_r
    (substitute 1 (shift 0 1 on_l)
      (substitute 2 (shift 0 1 (shift 0 1 C))
        (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 b)))
          (substitute 4
            (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
            (substitute 5
              (shift 0 1
                (shift 0 1
                  (shift 0 1
                    (shift 0 1
                      (shift 0 1 A)))))
              church_inr_payload)))))

theorem church_ctx_lookup_length_lt {Γ : Ctx} {i : Idx} {A : Term}
    (h : Γ.lookup i = some A) :
    i < Γ.length := by
  induction Γ generalizing i A with
  | nil =>
      cases i with
      | zero =>
          cases h
      | succ i =>
          cases h
  | cons head tail ih =>
      cases i with
      | zero =>
          exact Nat.zero_lt_succ tail.length
      | succ i =>
          unfold Ctx.lookup at h
          cases hlookup : Ctx.lookup tail i with
          | none =>
              rw [hlookup] at h
              cases h
          | some B =>
              exact Nat.succ_lt_succ (ih hlookup)

theorem hasType_closed_at_context_length {Γ : Ctx} {t A : Term}
    (h : HasType Γ t A) :
    ClosedAt Γ.length t := by
  induction h with
  | sortRule Γ =>
      exact ClosedAt.sortClosed
  | varRule Γ i A hlookup =>
      exact ClosedAt.varClosed (church_ctx_lookup_length_lt hlookup)
  | piRule Γ dom cod hdom hcod ihdom ihcod =>
      apply ClosedAt.piClosed
      · exact ihdom
      · change ClosedAt (((shift 0 1 dom) :: Γ).length) cod
        exact ihcod
  | lamRule Γ dom body cod hdom hbody ihdom ihbody =>
      apply ClosedAt.lamClosed
      · exact ihdom
      · change ClosedAt (((shift 0 1 dom) :: Γ).length) body
        exact ihbody
  | appRule Γ f a dom cod hf ha ihf iha =>
      exact ClosedAt.appClosed ihf iha

theorem church_case_either_payload_closed4 :
    ClosedAt 4 church_case_either_payload := by
  unfold church_case_either_payload
  apply ClosedAt.appClosed
  · apply ClosedAt.appClosed
    · apply ClosedAt.appClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 3
    · apply ClosedAt.varClosed
      exact Nat.lt_trans (Nat.lt_succ_self 1)
        (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 3

theorem church_case_either_payload_closed5 :
    ClosedAt 5 church_case_either_payload := by
  exact closedAt_succ 4 church_case_either_payload
    church_case_either_payload_closed4

theorem church_inl_payload_closed4 :
    ClosedAt 4 church_inl_payload := by
  unfold church_inl_payload
  apply ClosedAt.appClosed
  · apply ClosedAt.varClosed
    exact Nat.lt_trans (Nat.lt_succ_self 1)
      (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
  · apply ClosedAt.varClosed
    exact Nat.lt_succ_self 3

theorem church_inl_payload_closed5 :
    ClosedAt 5 church_inl_payload := by
  exact closedAt_succ 4 church_inl_payload church_inl_payload_closed4

theorem church_inr_payload_closed4 :
    ClosedAt 4 church_inr_payload := by
  unfold church_inr_payload
  apply ClosedAt.appClosed
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 3
  · apply ClosedAt.varClosed
    exact Nat.lt_succ_self 3

theorem church_inr_payload_closed5 :
    ClosedAt 5 church_inr_payload := by
  exact closedAt_succ 4 church_inr_payload church_inr_payload_closed4

theorem church_either_type_typed :
    HasType [] church_either_type Term.sort := by
  exact inferTypeCtx_sound [] church_either_type Term.sort rfl

theorem church_inl_typed :
    HasType [] church_inl church_inl_type := by
  exact inferTypeCtx_sound [] church_inl church_inl_type rfl

theorem church_inr_typed :
    HasType [] church_inr church_inr_type := by
  exact inferTypeCtx_sound [] church_inr church_inr_type rfl

theorem church_case_either_typed :
    HasType [] church_case_either church_case_either_type := by
  exact inferTypeCtx_sound [] church_case_either church_case_either_type rfl

theorem church_case_either_payload_normalize
    (A B C e on_l on_r : Term)
    (_hA : ClosedAt 0 A) (_hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (he : ClosedAt 0 e) (hon_l : ClosedAt 0 on_l)
    (_hon_r : ClosedAt 0 on_r) :
    church_case_either_payload_subst A B C e on_l on_r =
      Term.app (Term.app (Term.app e C) on_l) on_r := by
  unfold church_case_either_payload_subst
  rw [substitute_closed 5
    (shift 0 1
      (shift 0 1
        (shift 0 1
          (shift 0 1
            (shift 0 1 A)))))
    church_case_either_payload
    church_case_either_payload_closed5]
  rw [substitute_closed 4
    (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
    church_case_either_payload
    church_case_either_payload_closed4]
  unfold church_case_either_payload
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (substitute 2 (shift 0 1 (shift 0 1 e))
          (Term.app
            (Term.app
              (Term.app (Term.var 2)
                (shift 0 1 (shift 0 1 (shift 0 1 C))))
              (Term.var 1))
            (Term.var 0)))) =
      Term.app (Term.app (Term.app e C) on_l) on_r
  rw [shift_closed 0 C hC]
  rw [shift_closed 0 C hC]
  rw [shift_closed 0 C hC]
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (Term.app
          (Term.app
            (Term.app (substitute 2 (shift 0 1 (shift 0 1 e)) (Term.var 2))
              (substitute 2 (shift 0 1 (shift 0 1 e)) C))
            (Term.var 1))
          (Term.var 0))) =
      Term.app (Term.app (Term.app e C) on_l) on_r
  rw [substitute_closed 2 (shift 0 1 (shift 0 1 e)) C
    (closedAt_zero_at 2 C hC)]
  rw [shift_closed 0 e he]
  rw [shift_closed 0 e he]
  change substitute 0 on_r
      (Term.app
        (Term.app
          (Term.app
            (substitute 1 (shift 0 1 on_l) e)
            (substitute 1 (shift 0 1 on_l) C))
          (shift 0 1 on_l))
        (Term.var 0)) =
      Term.app (Term.app (Term.app e C) on_l) on_r
  rw [substitute_closed 1 (shift 0 1 on_l) e
    (closedAt_zero_at 1 e he)]
  rw [substitute_closed 1 (shift 0 1 on_l) C
    (closedAt_zero_at 1 C hC)]
  rw [shift_closed 0 on_l hon_l]
  change Term.app
      (Term.app
        (Term.app (substitute 0 on_r e) (substitute 0 on_r C))
        (substitute 0 on_r on_l))
      on_r =
      Term.app (Term.app (Term.app e C) on_l) on_r
  rw [substitute_closed 0 on_r e he]
  rw [substitute_closed 0 on_r C hC]
  rw [substitute_closed 0 on_r on_l hon_l]

theorem church_inl_payload_normalize
    (A B C a on_l on_r : Term)
    (_hA : ClosedAt 0 A) (_hB : ClosedAt 0 B) (_hC : ClosedAt 0 C)
    (ha : ClosedAt 0 a) (hon_l : ClosedAt 0 on_l)
    (_hon_r : ClosedAt 0 on_r) :
    church_inl_payload_subst A B C a on_l on_r =
      Term.app on_l a := by
  unfold church_inl_payload_subst
  rw [substitute_closed 5
    (shift 0 1
      (shift 0 1
        (shift 0 1
          (shift 0 1
            (shift 0 1 A)))))
    church_inl_payload
    church_inl_payload_closed5]
  rw [substitute_closed 4
    (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
    church_inl_payload
    church_inl_payload_closed4]
  unfold church_inl_payload
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (substitute 2 (shift 0 1 (shift 0 1 C))
          (Term.app (Term.var 1)
            (shift 0 1 (shift 0 1 (shift 0 1 a)))))) =
      Term.app on_l a
  rw [shift_closed 0 a ha]
  rw [shift_closed 0 a ha]
  rw [shift_closed 0 a ha]
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (Term.app
          (Term.var 1)
          (substitute 2 (shift 0 1 (shift 0 1 C)) a))) =
      Term.app on_l a
  rw [substitute_closed 2 (shift 0 1 (shift 0 1 C)) a
    (closedAt_zero_at 2 a ha)]
  change substitute 0 on_r
      (Term.app
        (shift 0 1 on_l)
        (substitute 1 (shift 0 1 on_l) a)) =
      Term.app on_l a
  rw [substitute_closed 1 (shift 0 1 on_l) a
    (closedAt_zero_at 1 a ha)]
  rw [shift_closed 0 on_l hon_l]
  change Term.app
      (substitute 0 on_r on_l)
      (substitute 0 on_r a) =
      Term.app on_l a
  rw [substitute_closed 0 on_r on_l hon_l]
  rw [substitute_closed 0 on_r a ha]

theorem church_inr_payload_normalize
    (A B C b on_l on_r : Term)
    (_hA : ClosedAt 0 A) (_hB : ClosedAt 0 B) (_hC : ClosedAt 0 C)
    (hb : ClosedAt 0 b) (_hon_l : ClosedAt 0 on_l)
    (_hon_r : ClosedAt 0 on_r) :
    church_inr_payload_subst A B C b on_l on_r =
      Term.app on_r b := by
  unfold church_inr_payload_subst
  rw [substitute_closed 5
    (shift 0 1
      (shift 0 1
        (shift 0 1
          (shift 0 1
            (shift 0 1 A)))))
    church_inr_payload
    church_inr_payload_closed5]
  rw [substitute_closed 4
    (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
    church_inr_payload
    church_inr_payload_closed4]
  unfold church_inr_payload
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (substitute 2 (shift 0 1 (shift 0 1 C))
          (Term.app (Term.var 0)
            (shift 0 1 (shift 0 1 (shift 0 1 b)))))) =
      Term.app on_r b
  rw [shift_closed 0 b hb]
  rw [shift_closed 0 b hb]
  rw [shift_closed 0 b hb]
  change substitute 0 on_r
      (substitute 1 (shift 0 1 on_l)
        (Term.app
          (Term.var 0)
          (substitute 2 (shift 0 1 (shift 0 1 C)) b))) =
      Term.app on_r b
  rw [substitute_closed 2 (shift 0 1 (shift 0 1 C)) b
    (closedAt_zero_at 2 b hb)]
  change substitute 0 on_r
      (Term.app
        (Term.var 0)
        (substitute 1 (shift 0 1 on_l) b)) =
      Term.app on_r b
  rw [substitute_closed 1 (shift 0 1 on_l) b
    (closedAt_zero_at 1 b hb)]
  change Term.app on_r
      (substitute 0 on_r b) =
      Term.app on_r b
  rw [substitute_closed 0 on_r b hb]

theorem church_case_either_head
    (A B C e on_l on_r : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (he : ClosedAt 0 e) (hon_l : ClosedAt 0 on_l)
    (hon_r : ClosedAt 0 on_r) :
    BetaStarStep
      (church_case_either_apply A B C e on_l on_r)
      (Term.app (Term.app (Term.app e C) on_l) on_r) := by
  unfold church_case_either_apply church_case_either
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ e
          (BetaStep.congApp1 _ _ C
            (BetaStep.congApp1 _ _ B
              (BetaStep.beta _ _ A)))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ e
          (BetaStep.congApp1 _ _ C
            (BetaStep.beta _ _ B))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ e
          (BetaStep.beta _ _ C)))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.beta _ _ e))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r (BetaStep.beta _ _ on_l)
  apply BetaStarStep.step
  · exact BetaStep.beta _ _ on_r
  change
    BetaStarStep
      (church_case_either_payload_subst A B C e on_l on_r)
      (Term.app (Term.app (Term.app e C) on_l) on_r)
  rw [church_case_either_payload_normalize A B C e on_l on_r
    hA hB hC he hon_l hon_r]
  exact BetaStarStep.refl
    (Term.app (Term.app (Term.app e C) on_l) on_r)

theorem church_inl_elim
    (A B C a on_l on_r : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (ha : ClosedAt 0 a) (hon_l : ClosedAt 0 on_l)
    (hon_r : ClosedAt 0 on_r) :
    BetaStarStep
      (Term.app (Term.app (Term.app (church_inl_apply A B a) C) on_l) on_r)
      (Term.app on_l a) := by
  unfold church_inl_apply church_inl
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.congApp1 _ _ a
            (BetaStep.congApp1 _ _ B
              (BetaStep.beta _ _ A)))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.congApp1 _ _ a
            (BetaStep.beta _ _ B))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.beta _ _ a)))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.beta _ _ C))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r (BetaStep.beta _ _ on_l)
  apply BetaStarStep.step
  · exact BetaStep.beta _ _ on_r
  change
    BetaStarStep
      (church_inl_payload_subst A B C a on_l on_r)
      (Term.app on_l a)
  rw [church_inl_payload_normalize A B C a on_l on_r
    hA hB hC ha hon_l hon_r]
  exact BetaStarStep.refl (Term.app on_l a)

theorem church_inr_elim
    (A B C b on_l on_r : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (hb : ClosedAt 0 b) (hon_l : ClosedAt 0 on_l)
    (hon_r : ClosedAt 0 on_r) :
    BetaStarStep
      (Term.app (Term.app (Term.app (church_inr_apply A B b) C) on_l) on_r)
      (Term.app on_r b) := by
  unfold church_inr_apply church_inr
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.congApp1 _ _ b
            (BetaStep.congApp1 _ _ B
              (BetaStep.beta _ _ A)))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.congApp1 _ _ b
            (BetaStep.beta _ _ B))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.congApp1 _ _ C
          (BetaStep.beta _ _ b)))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r
      (BetaStep.congApp1 _ _ on_l
        (BetaStep.beta _ _ C))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ on_r (BetaStep.beta _ _ on_l)
  apply BetaStarStep.step
  · exact BetaStep.beta _ _ on_r
  change
    BetaStarStep
      (church_inr_payload_subst A B C b on_l on_r)
      (Term.app on_r b)
  rw [church_inr_payload_normalize A B C b on_l on_r
    hA hB hC hb hon_l hon_r]
  exact BetaStarStep.refl (Term.app on_r b)

theorem church_case_inl
    (A B C a on_l on_r : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (ha : ClosedAt 0 a) (hon_l : ClosedAt 0 on_l)
    (hon_r : ClosedAt 0 on_r) :
    BetaStarStep
      (church_case_either_apply A B C (church_inl_apply A B a) on_l on_r)
      (Term.app on_l a) := by
  exact betaStar_trans
    (church_case_either_head A B C (church_inl_apply A B a) on_l on_r
      hA hB hC
      (ClosedAt.appClosed
        (ClosedAt.appClosed
          (ClosedAt.appClosed
            (closedAt_zero_at 0 church_inl
              (hasType_closed_at_context_length church_inl_typed))
            hA)
          hB)
        ha)
      hon_l hon_r)
    (church_inl_elim A B C a on_l on_r hA hB hC ha hon_l hon_r)

theorem church_case_inr
    (A B C b on_l on_r : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B) (hC : ClosedAt 0 C)
    (hb : ClosedAt 0 b) (hon_l : ClosedAt 0 on_l)
    (hon_r : ClosedAt 0 on_r) :
    BetaConv
      (church_case_either_apply A B C (church_inr_apply A B b) on_l on_r)
      (Term.app on_r b) := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_case_either_head A B C (church_inr_apply A B b) on_l on_r
        hA hB hC
        (ClosedAt.appClosed
          (ClosedAt.appClosed
            (ClosedAt.appClosed
              (closedAt_zero_at 0 church_inr
                (hasType_closed_at_context_length church_inr_typed))
              hA)
            hB)
          hb)
        hon_l hon_r)
      (church_inr_elim A B C b on_l on_r hA hB hC hb hon_l hon_r))

end BEDC.MetaCIC

import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.Confluence.Core

namespace BEDC.MetaCIC

abbrev churchPairValue (A B a b : Term) : Term :=
  Term.app (Term.app (Term.app (Term.app churchMkPairTm A) B) a) b

abbrev churchOptionNoneValue (A : Term) : Term :=
  Term.app churchNoneTm A

abbrev churchOptionSomeValue (A a : Term) : Term :=
  Term.app (Term.app churchSomeTm A) a

abbrev churchOptionCase (A R opt n s : Term) : Term :=
  Term.app (Term.app (Term.app (Term.app (Term.app churchCaseOptionTm A) R) opt) n) s

abbrev churchPairPayload : Term :=
  Term.app (Term.app (Term.var 0) (Term.var 3)) (Term.var 2)

theorem churchPairPayload_closed4 :
    ClosedAt 4 churchPairPayload := by
  unfold churchPairPayload
  apply ClosedAt.appClosed
  · apply ClosedAt.appClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 3
    · apply ClosedAt.varClosed
      exact Nat.lt_succ_self 3
  · apply ClosedAt.varClosed
    exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)

theorem churchPairPayload_closed5 :
    ClosedAt 5 churchPairPayload := by
  exact closedAt_succ 4 churchPairPayload churchPairPayload_closed4

theorem shift_zero_twice_closed (t : Term) (h : ClosedAt 0 t) :
    shift 0 1 (shift 0 1 t) = t := by
  rw [shift_closed 0 t h]
  rw [shift_closed 0 t h]

theorem shift_zero_three_closed (t : Term) (h : ClosedAt 0 t) :
    shift 0 1 (shift 0 1 (shift 0 1 t)) = t := by
  rw [shift_zero_twice_closed t h]
  rw [shift_closed 0 t h]

theorem shift_zero_four_closed (t : Term) (h : ClosedAt 0 t) :
    shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 t))) = t := by
  rw [shift_zero_three_closed t h]
  rw [shift_closed 0 t h]

theorem shift_zero_five_closed (t : Term) (h : ClosedAt 0 t) :
    shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 t)))) = t := by
  rw [shift_zero_four_closed t h]
  rw [shift_closed 0 t h]

theorem churchPairPayload_core_normalize (a b R k : Term)
    (ha : ClosedAt 0 a) (hb : ClosedAt 0 b) :
    substitute 0 k
      (substitute 1 (shift 0 1 R)
        (substitute 2 (shift 0 1 b)
          (substitute 3 a churchPairPayload))) =
    Term.app (Term.app k a) b := by
  unfold churchPairPayload
  change substitute 0 k
      (substitute 1 (shift 0 1 R)
        (substitute 2 (shift 0 1 b)
          (Term.app (Term.app (Term.var 0) a) (Term.var 2)))) =
    Term.app (Term.app k a) b
  change substitute 0 k
      (substitute 1 (shift 0 1 R)
        (Term.app
          (Term.app (Term.var 0) (substitute 2 (shift 0 1 b) a))
          (shift 0 1 b))) =
    Term.app (Term.app k a) b
  rw [substitute_closed 2 (shift 0 1 b) a (closedAt_zero_at 2 a ha)]
  rw [shift_closed 0 b hb]
  change substitute 0 k
      (Term.app
        (Term.app (Term.var 0) (substitute 1 (shift 0 1 R) a))
        (substitute 1 (shift 0 1 R) b)) =
    Term.app (Term.app k a) b
  rw [substitute_closed 1 (shift 0 1 R) a (closedAt_zero_at 1 a ha)]
  rw [substitute_closed 1 (shift 0 1 R) b (closedAt_zero_at 1 b hb)]
  change Term.app (Term.app k (substitute 0 k a)) (substitute 0 k b) =
    Term.app (Term.app k a) b
  rw [substitute_closed 0 k a ha]
  rw [substitute_closed 0 k b hb]

theorem churchPairPayload_normalize (A B a b R k : Term)
    (_hA : ClosedAt 0 A) (_hB : ClosedAt 0 B)
    (ha : ClosedAt 0 a) (hb : ClosedAt 0 b) :
    substitute 0 k
      (substitute 1 (shift 0 1 R)
        (substitute 2 (shift 0 1 (shift 0 1 b))
          (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 a)))
            (substitute 4 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
              (substitute 5 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 A)))))
                churchPairPayload))))) =
    Term.app (Term.app k a) b := by
  rw [substitute_closed 5
    (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 A)))))
    churchPairPayload churchPairPayload_closed5]
  rw [substitute_closed 4
    (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
    churchPairPayload churchPairPayload_closed4]
  rw [shift_zero_three_closed a ha]
  rw [shift_zero_twice_closed b hb]
  unfold churchPairPayload
  change substitute 0 k
      (substitute 1 (shift 0 1 R)
        (substitute 2 b
          (Term.app (Term.app (Term.var 0) a) (Term.var 2)))) =
    Term.app (Term.app k a) b
  change substitute 0 k
      (substitute 1 (shift 0 1 R)
        (Term.app
          (Term.app (Term.var 0) (substitute 2 b a))
          b)) =
    Term.app (Term.app k a) b
  rw [substitute_closed 2 b a (closedAt_zero_at 2 a ha)]
  change substitute 0 k
      (Term.app
        (Term.app (Term.var 0) (substitute 1 (shift 0 1 R) a))
        (substitute 1 (shift 0 1 R) b)) =
    Term.app (Term.app k a) b
  rw [substitute_closed 1 (shift 0 1 R) a (closedAt_zero_at 1 a ha)]
  rw [substitute_closed 1 (shift 0 1 R) b (closedAt_zero_at 1 b hb)]
  change Term.app (Term.app k (substitute 0 k a)) (substitute 0 k b) =
    Term.app (Term.app k a) b
  rw [substitute_closed 0 k a ha]
  rw [substitute_closed 0 k b hb]

theorem church_true_proj (X x y : Term)
    (hX : ClosedAt 0 X) (hx : ClosedAt 0 x) (_hy : ClosedAt 0 y) :
    BetaStarStep (Term.app (Term.app (Term.app churchTrueTm X) x) y) x := by
  unfold churchTrueTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ y
      (BetaStep.congApp1 _ _ x
        (BetaStep.beta Term.sort
          (Term.lam (Term.var 0)
            (Term.lam (Term.var 1) (Term.var 1)))
          X))
  unfold substitute
  rw [shift_closed 0 X hX]
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ y
      (BetaStep.beta X (Term.lam X (Term.var 1)) x)
  unfold substitute
  rw [shift_closed 0 x hx]
  rw [substitute_closed 0 x X hX]
  apply BetaStarStep.step
  · exact BetaStep.beta X x y
  rw [substitute_closed 0 y x hx]
  exact BetaStarStep.refl x

theorem church_false_proj (X x y : Term)
    (hX : ClosedAt 0 X) (_hx : ClosedAt 0 x) (_hy : ClosedAt 0 y) :
    BetaStarStep (Term.app (Term.app (Term.app churchFalseTm X) x) y) y := by
  unfold churchFalseTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ y
      (BetaStep.congApp1 _ _ x
        (BetaStep.beta Term.sort
          (Term.lam (Term.var 0)
            (Term.lam (Term.var 1) (Term.var 0)))
          X))
  unfold substitute
  rw [shift_closed 0 X hX]
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ y
      (BetaStep.beta X (Term.lam X (Term.var 0)) x)
  unfold substitute
  rw [substitute_closed 0 x X hX]
  apply BetaStarStep.step
  · exact BetaStep.beta X (Term.var 0) y
  exact BetaStarStep.refl y

theorem church_zero_apply (X f x : Term)
    (hX : ClosedAt 0 X) (_hf : ClosedAt 0 f) (_hx : ClosedAt 0 x) :
    BetaStarStep (Term.app (Term.app (Term.app churchZeroTm X) f) x) x := by
  unfold churchZeroTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.congApp1 _ _ f
        (BetaStep.beta Term.sort
          (Term.lam
            (Term.pi (Term.var 0) (Term.var 1))
            (Term.lam (Term.var 1) (Term.var 0)))
          X))
  unfold substitute
  rw [shift_closed 0 X hX]
  unfold substitute
  rw [shift_closed 0 X hX]
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x (BetaStep.beta _ _ f)
  change
    BetaStarStep
      (Term.app (Term.lam (substitute 0 f X) (Term.var 0)) x)
      x
  rw [substitute_closed 0 f X hX]
  apply BetaStarStep.step
  · exact BetaStep.beta X (Term.var 0) x
  exact BetaStarStep.refl x

theorem church_one_apply (X f x : Term)
    (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) (_hx : ClosedAt 0 x) :
    BetaStarStep (Term.app (Term.app (Term.app churchOneTm X) f) x) (Term.app f x) := by
  unfold churchOneTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.congApp1 _ _ f
        (BetaStep.beta Term.sort
          (Term.lam
            (Term.pi (Term.var 0) (Term.var 1))
            (Term.lam (Term.var 1)
              (Term.app (Term.var 1) (Term.var 0))))
          X))
  unfold substitute
  rw [shift_closed 0 X hX]
  unfold substitute
  rw [shift_closed 0 X hX]
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x (BetaStep.beta _ _ f)
  change
    BetaStarStep
      (Term.app
        (Term.lam (substitute 0 f X)
          (Term.app (shift 0 1 f) (Term.var 0)))
        x)
      (Term.app f x)
  rw [substitute_closed 0 f X hX]
  apply BetaStarStep.step
  · exact BetaStep.beta X (Term.app (shift 0 1 f) (Term.var 0)) x
  unfold substitute
  rw [shift_closed 0 f hf]
  rw [substitute_closed 0 x f hf]
  exact BetaStarStep.refl (Term.app f x)

theorem poly_identity_apply (X x : Term)
    (_hX : ClosedAt 0 X) (_hx : ClosedAt 0 x) :
    BetaStarStep (Term.app (Term.app churchIdentityTm X) x) x := by
  unfold churchIdentityTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.beta Term.sort (Term.lam (Term.var 0) (Term.var 0)) X)
  apply BetaStarStep.step
  · exact BetaStep.beta X (Term.var 0) x
  exact BetaStarStep.refl x

theorem church_pair_value_to_selector (A B a b R k : Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B)
    (ha : ClosedAt 0 a) (hb : ClosedAt 0 b) :
    BetaStarStep
      (Term.app (Term.app (churchPairValue A B a b) R) k)
      (Term.app (Term.app k a) b) := by
  unfold churchPairValue churchMkPairTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ k
      (BetaStep.congApp1 _ _ R
        (BetaStep.congApp1 _ _ b
          (BetaStep.congApp1 _ _ a
            (BetaStep.congApp1 _ _ B
              (BetaStep.beta _ _ A)))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ k
      (BetaStep.congApp1 _ _ R
        (BetaStep.congApp1 _ _ b
          (BetaStep.congApp1 _ _ a
            (BetaStep.beta _ _ B))))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ k
      (BetaStep.congApp1 _ _ R
        (BetaStep.congApp1 _ _ b
          (BetaStep.beta _ _ a)))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ k
      (BetaStep.congApp1 _ _ R
        (BetaStep.beta _ _ b))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ k (BetaStep.beta _ _ R)
  apply BetaStarStep.step
  · exact BetaStep.beta _ _ k
  change
    BetaStarStep
      (substitute 0 k
        (substitute 1 (shift 0 1 R)
          (substitute 2 (shift 0 1 (shift 0 1 b))
            (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 a)))
              (substitute 4 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 B))))
                (substitute 5
                  (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 (shift 0 1 A)))))
                  churchPairPayload))))))
      (Term.app (Term.app k a) b)
  rw [churchPairPayload_normalize A B a b R k hA hB ha hb]
  exact BetaStarStep.refl (Term.app (Term.app k a) b)

end BEDC.MetaCIC

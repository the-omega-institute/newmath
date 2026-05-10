import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

private theorem PolynomialSingletonAddFold_cons_hsame {x : BHist} {xs ys : List BHist} :
    hsame (PolynomialSingletonAddFold xs) (PolynomialSingletonAddFold ys) ->
      hsame (PolynomialSingletonAddFold (x :: xs)) (PolynomialSingletonAddFold (x :: ys)) := by
  intro tailSame
  exact congrArg (fun u : BHist => append x u) tailSame

private theorem PolynomialSingletonRawAdd_zero_remainder_empty_addFold_empty {t : List BHist} :
    PolynomialZeroRemainder t ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd t [])) BHist.Empty := by
  intro zeroRemainder
  induction zeroRemainder with
  | nil =>
      unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonZero
      exact hsame_refl BHist.Empty
  | cons headEmpty _tailZero ih =>
      unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
      exact append_eq_empty_iff.mpr
        (And.intro
          (append_eq_empty_iff.mpr (And.intro headEmpty (hsame_refl BHist.Empty)))
          ih)

theorem PolynomialSingletonRawAdd_left_zero_tail_addFold_invariance {xs ys t : List BHist} :
    PolynomialZeroRemainder t ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (xs ++ t) ys))
        (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) ∧
        Cont (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) BHist.Empty
          (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro zeroTail
  have zeroTailRawAdd :
      forall {t ys : List BHist}, PolynomialZeroRemainder t ->
        hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd t ys))
          (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys)) := by
    intro t ys zeroRemainder
    induction zeroRemainder generalizing ys with
    | nil =>
        exact hsame_refl (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys))
    | cons headEmpty _tailZero ih =>
        cases ys with
        | nil =>
            exact hsame_trans
              (PolynomialSingletonRawAdd_zero_remainder_empty_addFold_empty
                (PolynomialZeroRemainder.cons headEmpty _tailZero))
              (hsame_symm (by
                unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonZero
                exact hsame_refl BHist.Empty))
        | cons y ys =>
            have tailSame := ih (ys := ys)
            cases headEmpty
            unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
            exact PolynomialSingletonAddFold_cons_hsame (x := append BHist.Empty y) tailSame
  induction xs generalizing ys with
  | nil =>
      exact And.intro (zeroTailRawAdd zeroTail)
        (cont_right_unit (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys)))
  | cons x xs ih =>
      cases ys with
      | nil =>
          have tailData := ih (ys := [])
          unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
          exact And.intro
            (congrArg (fun u : BHist => append (append x BHist.Empty) u) tailData.left)
            (cont_right_unit
              (PolynomialSingletonAdd (append x BHist.Empty)
                (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs []))))
      | cons y ys =>
          have tailData := ih (ys := ys)
          unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
          exact And.intro
            (congrArg (fun u : BHist => append (append x y) u) tailData.left)
            (cont_right_unit
              (PolynomialSingletonAdd (append x y)
                (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys))))

theorem PolynomialSingletonRawAdd_commutative_classified {xs ys : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
            (PolynomialSingletonRawAdd xs ys) (PolynomialSingletonRawAdd ys xs) ∧
          Cont (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) BHist.Empty
            (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro classifiedXS
  induction xs generalizing ys with
  | nil =>
      intro classifiedYS
      induction ys with
      | nil =>
          constructor
          · unfold PolynomialSingletonRawAdd
            exact classifiedXS
          · exact cont_right_unit (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] []))
      | cons y ys ih =>
          cases classifiedYS with
          | intro headClassified tailClassified =>
              have headSwap :
                  PolynomialSingletonClassifier (append BHist.Empty y) (append y BHist.Empty) :=
                (PolynomialSingletonClassifier_continuation_comm_closed
                  (hsame_refl BHist.Empty) headClassified.left (cont_intro rfl)
                  (cont_intro rfl)).right.right
              have tailSwap := ih tailClassified
              constructor
              · unfold PolynomialSingletonRawAdd
                exact And.intro headSwap tailSwap.left
              · exact cont_right_unit
                  (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] (y :: ys)))
  | cons x xs ih =>
      intro classifiedYS
      cases classifiedXS with
      | intro headXClassified tailXClassified =>
          cases ys with
          | nil =>
              have nilClassified :
                  BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier [] [] := by
                constructor
              have tailSwap := ih tailXClassified nilClassified
              have headSwap :
                  PolynomialSingletonClassifier (append x BHist.Empty) (append BHist.Empty x) :=
                (PolynomialSingletonClassifier_continuation_comm_closed headXClassified.left
                  (hsame_refl BHist.Empty) (cont_intro rfl) (cont_intro rfl)).right.right
              constructor
              · unfold PolynomialSingletonRawAdd
                exact And.intro headSwap tailSwap.left
              · exact cont_right_unit
                  (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (x :: xs) []))
          | cons y ys =>
              cases classifiedYS with
              | intro headYClassified tailYClassified =>
                  have headSwap :
                      PolynomialSingletonClassifier (append x y) (append y x) :=
                    (PolynomialSingletonClassifier_continuation_comm_closed
                      headXClassified.left headYClassified.left (cont_intro rfl)
                      (cont_intro rfl)).right.right
                  have tailSwap := ih tailXClassified tailYClassified
                  constructor
                  · unfold PolynomialSingletonRawAdd
                    exact And.intro headSwap tailSwap.left
                  · exact cont_right_unit
                      (PolynomialSingletonAddFold
                        (PolynomialSingletonRawAdd (x :: xs) (y :: ys)))

private theorem PolynomialSingletonRawAdd_right_zero_tail_addFold_context_invariance
    {xs ys t : List BHist} :
    PolynomialZeroRemainder t ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs (ys ++ t)))
        (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro zeroTail
  induction xs generalizing ys t with
  | nil =>
      induction ys with
      | nil =>
          exact PolynomialSingletonRawAddEmptyLeft_zero_tail_addFold_empty zeroTail
      | cons y ys ih =>
          unfold PolynomialSingletonRawAdd PolynomialSingletonRawAddEmptyLeft PolynomialSingletonAddFold
            PolynomialSingletonAdd
          exact congrArg (fun u : BHist => append (append BHist.Empty y) u) ih
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases t with
          | nil =>
              exact hsame_refl
                (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (x :: xs) []))
          | cons y t =>
              cases zeroTail with
              | cons headEmpty tailZero =>
                  unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
                  exact hsame_trans
                    (congrArg
                      (fun h : BHist =>
                        append h (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs t)))
                      (congrArg (append x) headEmpty))
                    (congrArg (fun u : BHist => append (append x BHist.Empty) u)
                      (ih (ys := []) tailZero))
      | cons y ys =>
          unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
          exact congrArg (fun u : BHist => append (append x y) u) (ih zeroTail)

theorem PolynomialSingletonRawAdd_two_sided_trim_compatibility {xs ys tx ty : List BHist} :
    PolynomialZeroRemainder tx -> PolynomialZeroRemainder ty ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (xs ++ tx) (ys ++ ty)))
        (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) ∧
        Cont (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) BHist.Empty
          (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro zeroLeft zeroRight
  have leftData :=
    PolynomialSingletonRawAdd_left_zero_tail_addFold_invariance
      (xs := xs) (ys := ys ++ ty) zeroLeft
  have rightData :=
    PolynomialSingletonRawAdd_right_zero_tail_addFold_context_invariance
      (xs := xs) (ys := ys) zeroRight
  exact And.intro
    (hsame_trans leftData.left rightData)
    (cont_right_unit (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)))

private theorem PolynomialSingletonRawAdd_associative_classified_aux {xs ys zs : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier zs zs ->
          BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
            (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs)
            (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd ys zs)) := by
  intro classifiedXS
  induction xs generalizing ys zs with
  | nil =>
      intro classifiedYS classifiedZS
      induction ys generalizing zs with
      | nil =>
          induction zs with
          | nil =>
              constructor
          | cons z zs ih =>
              cases classifiedZS with
              | intro headZClassified tailZClassified =>
                  change PolynomialSingletonClassifier (append BHist.Empty z)
                      (append BHist.Empty (append BHist.Empty z)) ∧
                    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                      (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd [] []) zs)
                      (PolynomialSingletonRawAdd [] (PolynomialSingletonRawAdd [] zs))
                  constructor
                  · have leftCarrier :
                        PolynomialSingletonCarrier (append BHist.Empty z) :=
                      append_eq_empty_iff.mpr
                        (And.intro (hsame_refl BHist.Empty) headZClassified.left)
                    have rightCarrier :
                        PolynomialSingletonCarrier (append BHist.Empty (append BHist.Empty z)) :=
                      append_eq_empty_iff.mpr
                        (And.intro (hsame_refl BHist.Empty)
                          (append_eq_empty_iff.mpr
                            (And.intro (hsame_refl BHist.Empty) headZClassified.left)))
                    exact And.intro leftCarrier
                      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                  · exact ih tailZClassified
      | cons y ys ih =>
          cases classifiedYS with
          | intro headYClassified tailYClassified =>
              cases zs with
              | nil =>
                  change PolynomialSingletonClassifier
                      (append (append BHist.Empty y) BHist.Empty)
                      (append BHist.Empty (append y BHist.Empty)) ∧
                    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                      (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd [] ys) [])
                      (PolynomialSingletonRawAdd [] (PolynomialSingletonRawAdd ys []))
                  constructor
                  · have yzHead :
                        PolynomialSingletonClassifier (append (append BHist.Empty y) BHist.Empty)
                          (append BHist.Empty (append y BHist.Empty)) :=
                      And.intro
                        (append_eq_empty_iff.mpr
                          (And.intro
                            (append_eq_empty_iff.mpr
                              (And.intro (hsame_refl BHist.Empty) headYClassified.left))
                            (hsame_refl BHist.Empty)))
                        (And.intro
                          (append_eq_empty_iff.mpr
                            (And.intro (hsame_refl BHist.Empty)
                              (append_eq_empty_iff.mpr
                                (And.intro headYClassified.left (hsame_refl BHist.Empty)))))
                          (hsame_trans
                            (append_eq_empty_iff.mpr
                              (And.intro
                                (append_eq_empty_iff.mpr
                                  (And.intro (hsame_refl BHist.Empty) headYClassified.left))
                                (hsame_refl BHist.Empty)))
                            (hsame_symm
                              (append_eq_empty_iff.mpr
                                (And.intro (hsame_refl BHist.Empty)
                                  (append_eq_empty_iff.mpr
                                    (And.intro headYClassified.left
                                      (hsame_refl BHist.Empty))))))))
                    exact yzHead
                  · exact ih tailYClassified (by constructor)
              | cons z zs =>
                  cases classifiedZS with
                  | intro headZClassified tailZClassified =>
                      change PolynomialSingletonClassifier (append (append BHist.Empty y) z)
                          (append BHist.Empty (append y z)) ∧
                        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                          (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd [] ys) zs)
                          (PolynomialSingletonRawAdd [] (PolynomialSingletonRawAdd ys zs))
                      constructor
                      · have leftCarrier :
                            PolynomialSingletonCarrier (append (append BHist.Empty y) z) :=
                          append_eq_empty_iff.mpr
                            (And.intro
                              (append_eq_empty_iff.mpr
                                (And.intro (hsame_refl BHist.Empty) headYClassified.left))
                              headZClassified.left)
                        have rightCarrier :
                            PolynomialSingletonCarrier (append BHist.Empty (append y z)) :=
                          append_eq_empty_iff.mpr
                            (And.intro (hsame_refl BHist.Empty)
                              (append_eq_empty_iff.mpr
                                (And.intro headYClassified.left headZClassified.left)))
                        exact And.intro leftCarrier
                          (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                      · exact ih tailYClassified tailZClassified
  | cons x xs ih =>
      intro classifiedYS classifiedZS
      cases classifiedXS with
      | intro headXClassified tailXClassified =>
          cases ys with
          | nil =>
              cases zs with
              | nil =>
                  change PolynomialSingletonClassifier
                      (append (append x BHist.Empty) BHist.Empty) (append x BHist.Empty) ∧
                    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                      (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs []) [])
                      (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd [] []))
                  constructor
                  · have leftCarrier :
                        PolynomialSingletonCarrier (append (append x BHist.Empty) BHist.Empty) :=
                      append_eq_empty_iff.mpr
                        (And.intro
                          (append_eq_empty_iff.mpr
                            (And.intro headXClassified.left (hsame_refl BHist.Empty)))
                          (hsame_refl BHist.Empty))
                    have rightCarrier :
                        PolynomialSingletonCarrier (append x BHist.Empty) :=
                      append_eq_empty_iff.mpr
                        (And.intro headXClassified.left (hsame_refl BHist.Empty))
                    exact And.intro leftCarrier
                      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                  · exact ih tailXClassified classifiedYS classifiedZS
              | cons z zs =>
                  cases classifiedZS with
                  | intro headZClassified tailZClassified =>
                      change PolynomialSingletonClassifier (append (append x BHist.Empty) z)
                          (append x (append BHist.Empty z)) ∧
                        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                          (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs []) zs)
                          (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd [] zs))
                      constructor
                      · have leftCarrier :
                            PolynomialSingletonCarrier (append (append x BHist.Empty) z) :=
                          append_eq_empty_iff.mpr
                            (And.intro
                              (append_eq_empty_iff.mpr
                                (And.intro headXClassified.left (hsame_refl BHist.Empty)))
                              headZClassified.left)
                        have rightCarrier :
                            PolynomialSingletonCarrier (append x (append BHist.Empty z)) :=
                          append_eq_empty_iff.mpr
                            (And.intro headXClassified.left
                              (append_eq_empty_iff.mpr
                                (And.intro (hsame_refl BHist.Empty) headZClassified.left)))
                        exact And.intro leftCarrier
                          (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                      · exact ih tailXClassified classifiedYS tailZClassified
          | cons y ys =>
              cases classifiedYS with
              | intro headYClassified tailYClassified =>
                  cases zs with
                  | nil =>
                      change PolynomialSingletonClassifier (append (append x y) BHist.Empty)
                          (append x (append y BHist.Empty)) ∧
                        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                          (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) [])
                          (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd ys []))
                      constructor
                      · have leftCarrier :
                            PolynomialSingletonCarrier (append (append x y) BHist.Empty) :=
                          append_eq_empty_iff.mpr
                            (And.intro
                              (append_eq_empty_iff.mpr
                                (And.intro headXClassified.left headYClassified.left))
                              (hsame_refl BHist.Empty))
                        have rightCarrier :
                            PolynomialSingletonCarrier (append x (append y BHist.Empty)) :=
                          append_eq_empty_iff.mpr
                            (And.intro headXClassified.left
                              (append_eq_empty_iff.mpr
                                (And.intro headYClassified.left (hsame_refl BHist.Empty))))
                        exact And.intro leftCarrier
                          (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                      · exact ih tailXClassified tailYClassified classifiedZS
                  | cons z zs =>
                      cases classifiedZS with
                      | intro headZClassified tailZClassified =>
                          change PolynomialSingletonClassifier (append (append x y) z)
                              (append x (append y z)) ∧
                            BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
                              (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs)
                              (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd ys zs))
                          constructor
                          · have leftCarrier :
                                PolynomialSingletonCarrier (append (append x y) z) :=
                              append_eq_empty_iff.mpr
                                (And.intro
                                  (append_eq_empty_iff.mpr
                                    (And.intro headXClassified.left headYClassified.left))
                                  headZClassified.left)
                            have rightCarrier :
                                PolynomialSingletonCarrier (append x (append y z)) :=
                              append_eq_empty_iff.mpr
                                (And.intro headXClassified.left
                                  (append_eq_empty_iff.mpr
                                    (And.intro headYClassified.left headZClassified.left)))
                            exact And.intro leftCarrier
                              (And.intro rightCarrier
                                (hsame_trans leftCarrier (hsame_symm rightCarrier)))
                          · exact ih tailXClassified tailYClassified tailZClassified

theorem PolynomialSingletonRawAdd_associative_classified {xs ys zs : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier zs zs ->
          BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
              (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs)
              (PolynomialSingletonRawAdd xs (PolynomialSingletonRawAdd ys zs)) ∧
            Cont (PolynomialSingletonAddFold
                (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs))
              BHist.Empty
              (PolynomialSingletonAddFold
                (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs)) := by
  intro classifiedXS classifiedYS classifiedZS
  exact And.intro
    (PolynomialSingletonRawAdd_associative_classified_aux classifiedXS classifiedYS classifiedZS)
    (cont_right_unit
      (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (PolynomialSingletonRawAdd xs ys) zs)))

end BEDC.Derived.PolynomialUp

import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.Beta.Conversion
import BEDC.MetaCIC.Evaluation.EvalClosed

namespace BEDC.MetaCIC

abbrev church_list_of (A : Term) : Term :=
  Term.pi Term.sort
    (Term.pi
      (Term.pi (shift 0 1 A)
        (Term.pi (Term.var 1) (Term.var 2)))
      (Term.pi (Term.var 1) (Term.var 2)))

def church_list_type : Term :=
  Term.lam Term.sort (church_list_of (Term.var 0))

abbrev church_list_type_ty : Term :=
  Term.pi Term.sort Term.sort

def church_nil : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam
        (Term.pi (Term.var 1)
          (Term.pi (Term.var 1) (Term.var 2)))
        (Term.lam (Term.var 1) (Term.var 0))))

abbrev church_nil_type : Term :=
  Term.pi Term.sort (church_list_of (Term.var 0))

def church_cons : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (church_list_of (Term.var 1))
        (Term.lam Term.sort
          (Term.lam
            (Term.pi (Term.var 3)
              (Term.pi (Term.var 1) (Term.var 2)))
            (Term.lam (Term.var 1)
              (Term.app
                (Term.app (Term.var 1) (Term.var 4))
                (Term.app
                  (Term.app
                    (Term.app (Term.var 3) (Term.var 2))
                    (Term.var 1))
                  (Term.var 0))))))))

abbrev church_cons_type : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi (church_list_of (Term.var 1))
        (church_list_of (Term.var 2))))

def church_fold : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (church_list_of (Term.var 1))
        (Term.lam
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 2) (Term.var 3)))
          (Term.lam (Term.var 2)
            (Term.app
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0))))))

abbrev church_fold_type : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (church_list_of (Term.var 1))
        (Term.pi
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 2) (Term.var 3)))
          (Term.pi (Term.var 2) (Term.var 3)))))

abbrev church_list_apply (A : Term) : Term :=
  Term.app church_list_type A

abbrev church_nil_apply (A : Term) : Term :=
  Term.app church_nil A

abbrev church_cons_apply (A x xs : Term) : Term :=
  Term.app (Term.app (Term.app church_cons A) x) xs

abbrev church_fold_apply (A B xs f init : Term) : Term :=
  Term.app (Term.app (Term.app (Term.app (Term.app church_fold A) B) xs) f) init

abbrev church_singleton (A x : Term) : Term :=
  church_cons_apply A x (church_nil_apply A)

abbrev church_three (A x y z : Term) : Term :=
  church_cons_apply A x
    (church_cons_apply A y
      (church_cons_apply A z (church_nil_apply A)))

theorem church_list_of_var0_typed :
    HasType [Term.sort] (church_list_of (Term.var 0)) Term.sort := by
  unfold church_list_of
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort]
  · apply HasType.piRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_list_type_typed :
    HasType [] church_list_type church_list_type_ty := by
  unfold church_list_type church_list_type_ty
  apply HasType.lamRule
  · exact HasType.sortRule []
  · exact church_list_of_var0_typed

theorem church_nil_typed :
    HasType [] church_nil church_nil_type := by
  unfold church_nil church_nil_type church_list_of
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.varRule
            rfl
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl

theorem church_list_of_var1_in_cons_ctx_typed :
    HasType [Term.var 1, Term.sort] (church_list_of (Term.var 1)) Term.sort := by
  unfold church_list_of
  apply HasType.piRule
  · exact HasType.sortRule [Term.var 1, Term.sort]
  · apply HasType.piRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_cons_type_typed :
    HasType [] church_cons_type Term.sort := by
  unfold church_cons_type church_list_of
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · exact church_list_of_var1_in_cons_ctx_typed
      · apply HasType.piRule
        · exact HasType.sortRule
            [shift 0 1 (church_list_of (Term.var 1)), Term.var 1, Term.sort]
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.varRule
                rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl

theorem church_cons_typed :
    HasType [] church_cons church_cons_type := by
  unfold church_cons church_cons_type
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · exact church_list_of_var1_in_cons_ctx_typed
      · unfold church_list_of
        apply HasType.lamRule
        · exact HasType.sortRule
            [shift 0 1 (church_list_of (Term.var 1)), Term.var 1, Term.sort]
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.varRule
                rfl
          · apply HasType.lamRule
            · apply HasType.varRule
              rfl
            · exact HasType.appRule
                [shift 0 1 (Term.var 1),
                  shift 0 1
                    (Term.pi (Term.var 3)
                      (Term.pi (Term.var 1) (Term.var 2))),
                  shift 0 1 Term.sort,
                  shift 0 1 (church_list_of (Term.var 1)),
                  shift 0 1 (Term.var 0),
                  shift 0 1 Term.sort]
                (Term.app (Term.var 1) (Term.var 4))
                (Term.app
                  (Term.app
                    (Term.app (Term.var 3) (Term.var 2))
                    (Term.var 1))
                  (Term.var 0))
                (Term.var 2)
                (Term.var 3)
                (HasType.appRule
                  [shift 0 1 (Term.var 1),
                    shift 0 1
                      (Term.pi (Term.var 3)
                        (Term.pi (Term.var 1) (Term.var 2))),
                    shift 0 1 Term.sort,
                    shift 0 1 (church_list_of (Term.var 1)),
                    shift 0 1 (Term.var 0),
                    shift 0 1 Term.sort]
                  (Term.var 1)
                  (Term.var 4)
                  (Term.var 5)
                  (Term.pi (Term.var 3) (Term.var 4))
                  (HasType.varRule
                    [shift 0 1 (Term.var 1),
                      shift 0 1
                        (Term.pi (Term.var 3)
                          (Term.pi (Term.var 1) (Term.var 2))),
                      shift 0 1 Term.sort,
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 (Term.var 0),
                      shift 0 1 Term.sort]
                    1
                    (Term.pi (Term.var 5)
                      (Term.pi (Term.var 3) (Term.var 4)))
                    rfl)
                  (HasType.varRule
                    [shift 0 1 (Term.var 1),
                      shift 0 1
                        (Term.pi (Term.var 3)
                          (Term.pi (Term.var 1) (Term.var 2))),
                      shift 0 1 Term.sort,
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 (Term.var 0),
                      shift 0 1 Term.sort]
                    4
                    (Term.var 5)
                    rfl))
                (HasType.appRule
                  [shift 0 1 (Term.var 1),
                    shift 0 1
                      (Term.pi (Term.var 3)
                        (Term.pi (Term.var 1) (Term.var 2))),
                    shift 0 1 Term.sort,
                    shift 0 1 (church_list_of (Term.var 1)),
                    shift 0 1 (Term.var 0),
                    shift 0 1 Term.sort]
                  (Term.app
                    (Term.app (Term.var 3) (Term.var 2))
                    (Term.var 1))
                  (Term.var 0)
                  (Term.var 2)
                  (Term.var 3)
                  (HasType.appRule
                    [shift 0 1 (Term.var 1),
                      shift 0 1
                        (Term.pi (Term.var 3)
                          (Term.pi (Term.var 1) (Term.var 2))),
                      shift 0 1 Term.sort,
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 (Term.var 0),
                      shift 0 1 Term.sort]
                    (Term.app (Term.var 3) (Term.var 2))
                    (Term.var 1)
                    (Term.pi (Term.var 5)
                      (Term.pi (Term.var 3) (Term.var 4)))
                    (Term.pi (Term.var 3) (Term.var 4))
                    (HasType.appRule
                      [shift 0 1 (Term.var 1),
                        shift 0 1
                          (Term.pi (Term.var 3)
                            (Term.pi (Term.var 1) (Term.var 2))),
                        shift 0 1 Term.sort,
                        shift 0 1 (church_list_of (Term.var 1)),
                        shift 0 1 (Term.var 0),
                        shift 0 1 Term.sort]
                      (Term.var 3)
                      (Term.var 2)
                      Term.sort
                      (Term.pi
                        (Term.pi (Term.var 6)
                          (Term.pi (Term.var 1) (Term.var 2)))
                        (Term.pi (Term.var 1) (Term.var 2)))
                      (HasType.varRule
                        [shift 0 1 (Term.var 1),
                          shift 0 1
                            (Term.pi (Term.var 3)
                              (Term.pi (Term.var 1) (Term.var 2))),
                          shift 0 1 Term.sort,
                          shift 0 1 (church_list_of (Term.var 1)),
                          shift 0 1 (Term.var 0),
                          shift 0 1 Term.sort]
                        3
                        (Term.pi Term.sort
                          (Term.pi
                            (Term.pi (Term.var 6)
                              (Term.pi (Term.var 1) (Term.var 2)))
                            (Term.pi (Term.var 1) (Term.var 2))))
                        rfl)
                      (HasType.varRule
                        [shift 0 1 (Term.var 1),
                          shift 0 1
                            (Term.pi (Term.var 3)
                              (Term.pi (Term.var 1) (Term.var 2))),
                          shift 0 1 Term.sort,
                          shift 0 1 (church_list_of (Term.var 1)),
                          shift 0 1 (Term.var 0),
                          shift 0 1 Term.sort]
                        2
                        Term.sort
                        rfl))
                    (HasType.varRule
                      [shift 0 1 (Term.var 1),
                        shift 0 1
                          (Term.pi (Term.var 3)
                            (Term.pi (Term.var 1) (Term.var 2))),
                        shift 0 1 Term.sort,
                        shift 0 1 (church_list_of (Term.var 1)),
                        shift 0 1 (Term.var 0),
                        shift 0 1 Term.sort]
                      1
                      (Term.pi (Term.var 5)
                        (Term.pi (Term.var 3) (Term.var 4)))
                      rfl))
                  (HasType.varRule
                    [shift 0 1 (Term.var 1),
                      shift 0 1
                        (Term.pi (Term.var 3)
                          (Term.pi (Term.var 1) (Term.var 2))),
                      shift 0 1 Term.sort,
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 (Term.var 0),
                      shift 0 1 Term.sort]
                    0
                    (Term.var 2)
                    rfl))

theorem church_fold_type_typed :
    HasType [] church_fold_type Term.sort := by
  unfold church_fold_type church_list_of
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · apply HasType.piRule
        · exact HasType.sortRule [Term.sort, Term.sort]
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.varRule
                rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
      · apply HasType.piRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.varRule
            rfl

theorem church_fold_typed :
    HasType [] church_fold church_fold_type := by
  unfold church_fold church_fold_type
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · unfold church_list_of
        apply HasType.piRule
        · exact HasType.sortRule [Term.sort, Term.sort]
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.varRule
                rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
      · apply HasType.lamRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
        · apply HasType.lamRule
          · apply HasType.varRule
            rfl
          · exact HasType.appRule
              [shift 0 1 (Term.var 2),
                shift 0 1
                  (Term.pi (Term.var 2)
                    (Term.pi (Term.var 2) (Term.var 3))),
                shift 0 1 (church_list_of (Term.var 1)),
                shift 0 1 Term.sort,
                shift 0 1 Term.sort]
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0)
              (Term.var 3)
              (Term.var 4)
              (HasType.appRule
                [shift 0 1 (Term.var 2),
                  shift 0 1
                    (Term.pi (Term.var 2)
                      (Term.pi (Term.var 2) (Term.var 3))),
                  shift 0 1 (church_list_of (Term.var 1)),
                  shift 0 1 Term.sort,
                  shift 0 1 Term.sort]
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1)
                (Term.pi (Term.var 4)
                  (Term.pi (Term.var 4) (Term.var 5)))
                (Term.pi (Term.var 4) (Term.var 5))
                (HasType.appRule
                  [shift 0 1 (Term.var 2),
                    shift 0 1
                      (Term.pi (Term.var 2)
                        (Term.pi (Term.var 2) (Term.var 3))),
                    shift 0 1 (church_list_of (Term.var 1)),
                    shift 0 1 Term.sort,
                    shift 0 1 Term.sort]
                  (Term.var 2)
                  (Term.var 3)
                  Term.sort
                  (Term.pi
                    (Term.pi (Term.var 5)
                      (Term.pi (Term.var 1) (Term.var 2)))
                    (Term.pi (Term.var 1) (Term.var 2)))
                  (HasType.varRule
                    [shift 0 1 (Term.var 2),
                      shift 0 1
                        (Term.pi (Term.var 2)
                          (Term.pi (Term.var 2) (Term.var 3))),
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 Term.sort,
                      shift 0 1 Term.sort]
                    2
                    (Term.pi Term.sort
                      (Term.pi
                        (Term.pi (Term.var 5)
                          (Term.pi (Term.var 1) (Term.var 2)))
                        (Term.pi (Term.var 1) (Term.var 2))))
                    rfl)
                  (HasType.varRule
                    [shift 0 1 (Term.var 2),
                      shift 0 1
                        (Term.pi (Term.var 2)
                          (Term.pi (Term.var 2) (Term.var 3))),
                      shift 0 1 (church_list_of (Term.var 1)),
                      shift 0 1 Term.sort,
                      shift 0 1 Term.sort]
                    3
                    Term.sort
                    rfl))
                (HasType.varRule
                  [shift 0 1 (Term.var 2),
                    shift 0 1
                      (Term.pi (Term.var 2)
                        (Term.pi (Term.var 2) (Term.var 3))),
                    shift 0 1 (church_list_of (Term.var 1)),
                    shift 0 1 Term.sort,
                    shift 0 1 Term.sort]
                  1
                  (Term.pi (Term.var 4)
                    (Term.pi (Term.var 4) (Term.var 5)))
                  rfl))
              (HasType.varRule
                [shift 0 1 (Term.var 2),
                  shift 0 1
                    (Term.pi (Term.var 2)
                      (Term.pi (Term.var 2) (Term.var 3))),
                  shift 0 1 (church_list_of (Term.var 1)),
                  shift 0 1 Term.sort,
                  shift 0 1 Term.sort]
                0
                (Term.var 3)
                rfl)

theorem church_nil_closed :
    ClosedAt 0 church_nil := by
  unfold church_nil
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.piClosed
        · apply ClosedAt.varClosed
          exact Nat.lt_succ_self 1
        · apply ClosedAt.piClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)
          · apply ClosedAt.varClosed
            exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)
        · apply ClosedAt.varClosed
          exact Nat.lt_trans
            (Nat.lt_succ_self 0)
            (Nat.lt_trans
              (Nat.lt_succ_self 1)
              (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)))

theorem church_nil_handler_type_after_A (A : Term) :
    substitute 1 A
      (Term.pi (Term.var 1)
        (Term.pi (Term.var 1) (Term.var 2))) =
    Term.pi A (Term.pi (Term.var 1) (Term.var 2)) := by
  unfold substitute
  rfl

theorem church_nil_self_beta :
    BetaStarStep church_nil church_nil := by
  exact BetaStarStep.refl church_nil

theorem church_fold_nil :
    BetaStarStep
      (church_fold_apply Term.sort Term.sort (church_nil_apply Term.sort)
        (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort := by
  change
    BetaStarStep
      (church_fold_apply Term.sort Term.sort (church_nil_apply Term.sort)
        (Term.lam Term.sort (Term.var 0)) Term.sort)
      (evalClosed 50
        (church_fold_apply Term.sort Term.sort (church_nil_apply Term.sort)
          (Term.lam Term.sort (Term.var 0)) Term.sort))
  exact evalClosed_betaStar_any 50
    (church_fold_apply Term.sort Term.sort (church_nil_apply Term.sort)
      (Term.lam Term.sort (Term.var 0)) Term.sort)

theorem church_fold_cons_singleton :
    BetaConv
      (church_fold_apply Term.sort Term.sort
        (church_cons_apply Term.sort Term.sort (church_nil_apply Term.sort))
        (Term.lam Term.sort (Term.var 0)) Term.sort)
      (Term.app Term.sort Term.sort) := by
  exact BetaConv.of_betaStar_left
    (show
      BetaStarStep
        (church_fold_apply Term.sort Term.sort
          (church_cons_apply Term.sort Term.sort (church_nil_apply Term.sort))
          (Term.lam Term.sort (Term.var 0)) Term.sort)
        (evalClosed 80
          (church_fold_apply Term.sort Term.sort
            (church_cons_apply Term.sort Term.sort (church_nil_apply Term.sort))
            (Term.lam Term.sort (Term.var 0)) Term.sort)) from
      evalClosed_betaStar_any 80
        (church_fold_apply Term.sort Term.sort
          (church_cons_apply Term.sort Term.sort (church_nil_apply Term.sort))
          (Term.lam Term.sort (Term.var 0)) Term.sort))

end BEDC.MetaCIC

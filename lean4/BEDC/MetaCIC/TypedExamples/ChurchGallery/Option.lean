import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

abbrev churchOptionATy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi
        (Term.pi (Term.var 2) (Term.var 2))
        (Term.var 2)))

abbrev churchOptionTy : Term :=
  Term.pi Term.sort churchOptionATy

abbrev churchNoneTy : Term :=
  churchOptionTy

abbrev churchNoneTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam
          (Term.pi (Term.var 2) (Term.var 2))
          (Term.var 1))))

abbrev churchSomeTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.var 2)))))

abbrev churchSomeTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.app (Term.var 0) (Term.var 3))))))

abbrev churchOptionAInCaseCtxTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi
        (Term.pi (Term.var 3) (Term.var 2))
        (Term.var 2)))

abbrev churchCaseOptionTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi churchOptionAInCaseCtxTy
        (Term.pi (Term.var 1)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 3))
            (Term.var 3)))))

abbrev churchCaseOptionTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam churchOptionAInCaseCtxTy
        (Term.lam (Term.var 1)
          (Term.lam
            (Term.pi (Term.var 3) (Term.var 3))
            (Term.app
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0))))))

theorem church_option_at_type :
    HasType [Term.sort] churchOptionATy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort]
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.varRule
        rfl

theorem church_option_type :
    HasType [] churchOptionTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact church_option_at_type

theorem church_none_type :
    HasType [] churchNoneTy Term.sort := by
  exact church_option_type

theorem church_none :
    HasType [] churchNoneTm churchNoneTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.lamRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.varRule
            rfl
        · apply HasType.varRule
          rfl

theorem church_some_type :
    HasType [] churchSomeTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · exact HasType.sortRule [Term.var 1, Term.sort]
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · apply HasType.varRule
            rfl

theorem church_some :
    HasType [] churchSomeTm churchSomeTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · exact HasType.sortRule [Term.var 1, Term.sort]
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · exact HasType.appRule
              [Term.pi (Term.var 4) (Term.var 3),
                Term.var 1,
                Term.sort,
                Term.var 1,
                Term.sort]
              (Term.var 0)
              (Term.var 3)
              (Term.var 4)
              (Term.var 3)
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 3),
                  Term.var 1,
                  Term.sort,
                  Term.var 1,
                  Term.sort]
                0
                (Term.pi (Term.var 4) (Term.var 3))
                rfl)
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 3),
                  Term.var 1,
                  Term.sort,
                  Term.var 1,
                  Term.sort]
                3
                (Term.var 4)
                rfl)

theorem church_option_in_case_ctx_type :
    HasType [Term.sort, Term.sort] churchOptionAInCaseCtxTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort, Term.sort]
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.varRule
        rfl

theorem church_case_option_type :
    HasType [] churchCaseOptionTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact church_option_in_case_ctx_type
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · apply HasType.varRule
            rfl

theorem church_case_option :
    HasType [] churchCaseOptionTm churchCaseOptionTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact church_option_in_case_ctx_type
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · exact HasType.appRule
              [Term.pi (Term.var 4) (Term.var 4),
                Term.var 2,
                shift 0 1 churchOptionAInCaseCtxTy,
                Term.sort,
                Term.sort]
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0)
              (Term.pi (Term.var 4) (Term.var 4))
              (Term.var 4)
              (HasType.appRule
                [Term.pi (Term.var 4) (Term.var 4),
                  Term.var 2,
                  shift 0 1 churchOptionAInCaseCtxTy,
                  Term.sort,
                  Term.sort]
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1)
                (Term.var 3)
                (Term.pi
                  (Term.pi (Term.var 5) (Term.var 5))
                  (Term.var 5))
                (HasType.appRule
                  [Term.pi (Term.var 4) (Term.var 4),
                    Term.var 2,
                    shift 0 1 churchOptionAInCaseCtxTy,
                    Term.sort,
                    Term.sort]
                  (Term.var 2)
                  (Term.var 3)
                  Term.sort
                  (Term.pi (Term.var 0)
                    (Term.pi
                      (Term.pi (Term.var 6) (Term.var 2))
                      (Term.var 2)))
                  (HasType.varRule
                    [Term.pi (Term.var 4) (Term.var 4),
                      Term.var 2,
                      shift 0 1 churchOptionAInCaseCtxTy,
                      Term.sort,
                      Term.sort]
                    2
                    (Term.pi Term.sort
                      (Term.pi (Term.var 0)
                        (Term.pi
                          (Term.pi (Term.var 6) (Term.var 2))
                          (Term.var 2))))
                    rfl)
                  (HasType.varRule
                    [Term.pi (Term.var 4) (Term.var 4),
                      Term.var 2,
                      shift 0 1 churchOptionAInCaseCtxTy,
                      Term.sort,
                      Term.sort]
                    3
                    Term.sort
                    rfl))
                (HasType.varRule
                  [Term.pi (Term.var 4) (Term.var 4),
                    Term.var 2,
                    shift 0 1 churchOptionAInCaseCtxTy,
                    Term.sort,
                    Term.sort]
                  1
                  (Term.var 3)
                  rfl))
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 4),
                  Term.var 2,
                  shift 0 1 churchOptionAInCaseCtxTy,
                  Term.sort,
                  Term.sort]
                0
                (Term.pi (Term.var 4) (Term.var 4))
                rfl)

end BEDC.MetaCIC

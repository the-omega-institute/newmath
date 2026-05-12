import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

theorem poly_identity_type :
    HasType []
      (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
      (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem poly_const_type :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort
        (Term.lam (Term.var 1) (Term.lam (Term.var 1) (Term.var 1)))))
      (Term.pi Term.sort (Term.pi Term.sort
        (Term.pi (Term.var 1) (Term.pi (Term.var 1) (Term.var 3))))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl

theorem poly_apply_type :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort
        (Term.lam (Term.pi (Term.var 1) (Term.var 1))
          (Term.lam (Term.var 2)
            (Term.app (Term.var 1) (Term.var 0))))))
      (Term.pi Term.sort (Term.pi Term.sort
        (Term.pi (Term.pi (Term.var 1) (Term.var 1))
          (Term.pi (Term.var 2) (Term.var 2))))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · exact HasType.appRule
            [Term.var 3,
              Term.pi (Term.var 2) (Term.var 2),
              Term.sort,
              Term.sort]
            (Term.var 1)
            (Term.var 0)
            (Term.var 3)
            (Term.var 3)
            (HasType.varRule
              [Term.var 3,
                Term.pi (Term.var 2) (Term.var 2),
                Term.sort,
                Term.sort]
              1
              (Term.pi (Term.var 3) (Term.var 3))
              rfl)
            (HasType.varRule
              [Term.var 3,
                Term.pi (Term.var 2) (Term.var 2),
                Term.sort,
                Term.sort]
              0
              (Term.var 3)
              rfl)

theorem poly_flip_type :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort
        (Term.lam (Term.pi (Term.var 2) (Term.pi (Term.var 2) (Term.var 2)))
          (Term.lam (Term.var 2)
            (Term.lam (Term.var 4)
              (Term.app
                (Term.app (Term.var 2) (Term.var 0))
                (Term.var 1))))))))
      (Term.pi Term.sort (Term.pi Term.sort (Term.pi Term.sort
        (Term.pi (Term.pi (Term.var 2) (Term.pi (Term.var 2) (Term.var 2)))
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 4) (Term.var 3))))))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact HasType.sortRule [Term.sort, Term.sort]
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
          · apply HasType.lamRule
            · apply HasType.varRule
              rfl
            · exact HasType.appRule
                [Term.var 5,
                  Term.var 3,
                  Term.pi (Term.var 3) (Term.pi (Term.var 3) (Term.var 3)),
                  Term.sort,
                  Term.sort,
                  Term.sort]
                (Term.app (Term.var 2) (Term.var 0))
                (Term.var 1)
                (Term.var 4)
                (Term.var 4)
                (HasType.appRule
                  [Term.var 5,
                    Term.var 3,
                    Term.pi (Term.var 3) (Term.pi (Term.var 3) (Term.var 3)),
                    Term.sort,
                    Term.sort,
                    Term.sort]
                  (Term.var 2)
                  (Term.var 0)
                  (Term.var 5)
                  (Term.pi (Term.var 5) (Term.var 5))
                  (HasType.varRule
                    [Term.var 5,
                      Term.var 3,
                      Term.pi (Term.var 3) (Term.pi (Term.var 3) (Term.var 3)),
                      Term.sort,
                      Term.sort,
                      Term.sort]
                    2
                    (Term.pi (Term.var 5)
                      (Term.pi (Term.var 5) (Term.var 5)))
                    rfl)
                  (HasType.varRule
                    [Term.var 5,
                      Term.var 3,
                      Term.pi (Term.var 3) (Term.pi (Term.var 3) (Term.var 3)),
                      Term.sort,
                      Term.sort,
                      Term.sort]
                    0
                    (Term.var 5)
                    rfl))
                (HasType.varRule
                  [Term.var 5,
                    Term.var 3,
                    Term.pi (Term.var 3) (Term.pi (Term.var 3) (Term.var 3)),
                    Term.sort,
                    Term.sort,
                    Term.sort]
                  1
                  (Term.var 4)
                  rfl)

theorem poly_compose_type :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort
        (Term.lam (Term.pi (Term.var 1) (Term.var 1))
          (Term.lam (Term.pi (Term.var 3) (Term.var 3))
            (Term.lam (Term.var 4)
              (Term.app (Term.var 2)
                (Term.app (Term.var 1) (Term.var 0)))))))))
      (Term.pi Term.sort (Term.pi Term.sort (Term.pi Term.sort
        (Term.pi (Term.pi (Term.var 1) (Term.var 1))
          (Term.pi (Term.pi (Term.var 3) (Term.var 3))
            (Term.pi (Term.var 4) (Term.var 3))))))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact HasType.sortRule [Term.sort, Term.sort]
      · apply HasType.lamRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.varRule
            rfl
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · apply HasType.lamRule
            · apply HasType.varRule
              rfl
            · exact HasType.appRule
                [Term.var 5,
                  Term.pi (Term.var 4) (Term.var 4),
                  Term.pi (Term.var 2) (Term.var 2),
                  Term.sort,
                  Term.sort,
                  Term.sort]
                (Term.var 2)
                (Term.app (Term.var 1) (Term.var 0))
                (Term.var 4)
                (Term.var 4)
                (HasType.varRule
                  [Term.var 5,
                    Term.pi (Term.var 4) (Term.var 4),
                    Term.pi (Term.var 2) (Term.var 2),
                    Term.sort,
                    Term.sort,
                    Term.sort]
                  2
                  (Term.pi (Term.var 4) (Term.var 4))
                  rfl)
                (HasType.appRule
                  [Term.var 5,
                    Term.pi (Term.var 4) (Term.var 4),
                    Term.pi (Term.var 2) (Term.var 2),
                    Term.sort,
                    Term.sort,
                    Term.sort]
                  (Term.var 1)
                  (Term.var 0)
                  (Term.var 5)
                  (Term.var 5)
                  (HasType.varRule
                    [Term.var 5,
                      Term.pi (Term.var 4) (Term.var 4),
                      Term.pi (Term.var 2) (Term.var 2),
                      Term.sort,
                      Term.sort,
                      Term.sort]
                    1
                    (Term.pi (Term.var 5) (Term.var 5))
                    rfl)
                  (HasType.varRule
                    [Term.var 5,
                      Term.pi (Term.var 4) (Term.var 4),
                      Term.pi (Term.var 2) (Term.var 2),
                      Term.sort,
                      Term.sort,
                      Term.sort]
                    0
                    (Term.var 5)
                    rfl))

theorem poly_identity_at_sort_type :
    HasType []
      (Term.app
        (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
        Term.sort)
      (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
    Term.sort
    Term.sort
    (Term.pi (Term.var 0) (Term.var 1))
    poly_identity_type
    (HasType.sortRule [])

end BEDC.MetaCIC

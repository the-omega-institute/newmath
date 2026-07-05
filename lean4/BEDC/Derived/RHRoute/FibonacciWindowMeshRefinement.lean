/-!
# Fibonacci-window mesh refinement

This file records the finite integer certificates behind the geometry of the
Fibonacci-hat Weil windows.  The analytic mesh is
`h_m = log(F_{m+2}) / F_m`; strict refinement is represented, after
exponentiating the monotone logarithm comparison, by the pure natural-number
inequality `F_{m+3}^{F_m} < F_{m+2}^{F_{m+1}}`.  The window
`log(F_{m+2})` grows with `m`.

These finite bricks are the geometric companion to the degree-3 Weil positivity
certificate.  They encode the necessary mesh-to-zero and window-to-infinity
shape of a density program for the log-hat tests.  The full fundamentality
statement is not asserted here; it is essentially the Riemann hypothesis.
-/

namespace BEDC.Derived.RHRoute.FibonacciWindowMeshRefinement

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => fib (Nat.succ n) + fib n

theorem fib_check : fib 5 = 5 ∧ fib 8 = 21 := by
  exact And.intro rfl rfl

theorem mesh_refine_3 : fib (3 + 3) ^ fib 3 < fib (3 + 2) ^ fib (3 + 1) := by
  exact Nat.le.intro (show (fib (3 + 3) ^ fib 3 + 1) + 60 = fib (3 + 2) ^ fib (3 + 1) by rfl)

theorem mesh_refine_4 : fib (4 + 3) ^ fib 4 < fib (4 + 2) ^ fib (4 + 1) := by
  exact Nat.le.intro (show (fib (4 + 3) ^ fib 4 + 1) + 30570 = fib (4 + 2) ^ fib (4 + 1) by rfl)

theorem mesh_refine_5 : fib (5 + 3) ^ fib 5 < fib (5 + 2) ^ fib (5 + 1) := by
  exact Nat.le.intro (show (fib (5 + 3) ^ fib 5 + 1) + 811646619 = fib (5 + 2) ^ fib (5 + 1) by rfl)

theorem mesh_refine_6 : fib (6 + 3) ^ fib 6 < fib (6 + 2) ^ fib (6 + 1) := by
  exact Nat.le.intro
    (show (fib (6 + 3) ^ fib 6 + 1) + 154470591945214564 = fib (6 + 2) ^ fib (6 + 1) by rfl)

theorem mesh_refine_7 : fib (7 + 3) ^ fib 7 < fib (7 + 2) ^ fib (7 + 1) := by
  exact Nat.le.intro
    (show (fib (7 + 3) ^ fib 7 + 1) + 144896287347392107580920538301608 =
      fib (7 + 2) ^ fib (7 + 1) by rfl)

theorem window_grows_3 : fib (3 + 2) < fib (3 + 3) := by
  exact Nat.le.intro (show (fib (3 + 2) + 1) + 2 = fib (3 + 3) by rfl)

theorem window_grows_4 : fib (4 + 2) < fib (4 + 3) := by
  exact Nat.le.intro (show (fib (4 + 2) + 1) + 4 = fib (4 + 3) by rfl)

theorem window_grows_5 : fib (5 + 2) < fib (5 + 3) := by
  exact Nat.le.intro (show (fib (5 + 2) + 1) + 7 = fib (5 + 3) by rfl)

theorem window_grows_6 : fib (6 + 2) < fib (6 + 3) := by
  exact Nat.le.intro (show (fib (6 + 2) + 1) + 12 = fib (6 + 3) by rfl)

theorem window_grows_7 : fib (7 + 2) < fib (7 + 3) := by
  exact Nat.le.intro (show (fib (7 + 2) + 1) + 20 = fib (7 + 3) by rfl)

theorem mesh_halves_3 : fib (3 + 5) ^ (2 * fib 3) < fib (3 + 2) ^ fib (3 + 3) := by
  exact Nat.le.intro
    (show (fib (3 + 5) ^ (2 * fib 3) + 1) + 196143 = fib (3 + 2) ^ fib (3 + 3) by rfl)

theorem mesh_halves_4 : fib (4 + 5) ^ (2 * fib 4) < fib (4 + 2) ^ fib (4 + 3) := by
  exact Nat.le.intro
    (show (fib (4 + 5) ^ (2 * fib 4) + 1) + 548211009471 = fib (4 + 2) ^ fib (4 + 3) by rfl)

theorem mesh_halves_5 : fib (5 + 5) ^ (2 * fib 5) < fib (5 + 2) ^ fib (5 + 3) := by
  exact Nat.le.intro
    (show (fib (5 + 5) ^ (2 * fib 5) + 1) + 247064275778288273563787 =
      fib (5 + 2) ^ fib (5 + 3) by rfl)

theorem mesh_halves_6 : fib (6 + 5) ^ (2 * fib 6) < fib (6 + 2) ^ fib (6 + 3) := by
  exact Nat.le.intro
    (show (fib (6 + 5) ^ (2 * fib 6) + 1) + 902518308877779694701814924466821275295726519 =
      fib (6 + 2) ^ fib (6 + 3) by rfl)

theorem mesh_halves_7 : fib (7 + 5) ^ (2 * fib 7) < fib (7 + 2) ^ fib (7 + 3) := by
  exact Nat.le.intro
    (show (fib (7 + 5) ^ (2 * fib 7) + 1) +
      1703493329567268465942478062403647803958821057736322891530469761396530525446831341567 =
        fib (7 + 2) ^ fib (7 + 3) by rfl)

#print axioms mesh_halves_3
#print axioms mesh_halves_4
#print axioms mesh_halves_5
#print axioms mesh_halves_6
#print axioms mesh_halves_7

theorem fibonacci_window_mesh_refinement_certificate :
    fib (3 + 3) ^ fib 3 < fib (3 + 2) ^ fib (3 + 1) ∧
      fib (4 + 3) ^ fib 4 < fib (4 + 2) ^ fib (4 + 1) ∧
      fib (5 + 3) ^ fib 5 < fib (5 + 2) ^ fib (5 + 1) ∧
      fib (6 + 3) ^ fib 6 < fib (6 + 2) ^ fib (6 + 1) ∧
      fib (7 + 3) ^ fib 7 < fib (7 + 2) ^ fib (7 + 1) ∧
      fib (3 + 2) < fib (3 + 3) ∧
      fib (4 + 2) < fib (4 + 3) ∧
      fib (5 + 2) < fib (5 + 3) ∧
      fib (6 + 2) < fib (6 + 3) ∧
      fib (7 + 2) < fib (7 + 3) ∧
      fib (3 + 5) ^ (2 * fib 3) < fib (3 + 2) ^ fib (3 + 3) ∧
      fib (4 + 5) ^ (2 * fib 4) < fib (4 + 2) ^ fib (4 + 3) ∧
      fib (5 + 5) ^ (2 * fib 5) < fib (5 + 2) ^ fib (5 + 3) ∧
      fib (6 + 5) ^ (2 * fib 6) < fib (6 + 2) ^ fib (6 + 3) ∧
      fib (7 + 5) ^ (2 * fib 7) < fib (7 + 2) ^ fib (7 + 3) := by
  exact And.intro mesh_refine_3
    (And.intro mesh_refine_4
      (And.intro mesh_refine_5
        (And.intro mesh_refine_6
          (And.intro mesh_refine_7
            (And.intro window_grows_3
              (And.intro window_grows_4
                (And.intro window_grows_5
                  (And.intro window_grows_6
                    (And.intro window_grows_7
                      (And.intro mesh_halves_3
                        (And.intro mesh_halves_4
                          (And.intro mesh_halves_5
                            (And.intro mesh_halves_6 mesh_halves_7)))))))))))))

end BEDC.Derived.RHRoute.FibonacciWindowMeshRefinement

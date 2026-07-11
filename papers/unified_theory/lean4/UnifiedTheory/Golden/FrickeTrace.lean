import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace UnifiedTheory

variable {R : Type*} [CommRing R]

/-- 2×2 trace identity: `tr(AB) + tr(adj(A) * B) = tr A * tr B`. -/
theorem trace_mul_add_trace_adjugate_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B).trace + (A.adjugate * B).trace = A.trace * B.trace := by
  simp only [Matrix.trace_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **SL₂ trace completion**: `tr(A⁻¹B) = tr A * tr B - tr(AB)`. -/
theorem SL2_trace_inv_mul (A B : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((↑(A⁻¹ * B) : Matrix (Fin 2) (Fin 2) R).trace)
      = (↑A : Matrix (Fin 2) (Fin 2) R).trace * (↑B : Matrix (Fin 2) (Fin 2) R).trace
        - ((↑A : Matrix (Fin 2) (Fin 2) R) * (↑B : Matrix (Fin 2) (Fin 2) R)).trace := by
  have hkey := trace_mul_add_trace_adjugate_mul
    (A := (↑A : Matrix (Fin 2) (Fin 2) R))
    (B := (↑B : Matrix (Fin 2) (Fin 2) R))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using hkey

end UnifiedTheory

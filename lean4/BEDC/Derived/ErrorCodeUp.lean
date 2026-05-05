import BEDC.FKernel.Unary

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

structure ErrorCodeMinimumDistanceDecoding where
  Code : BHist -> Prop
  rho : BHist -> BHist -> Prop
  delta : BHist -> BHist -> Nat
  d : Nat
  t : Nat
  d_pos : 0 < d
  radius_bound : t + t < d
  code_unary : forall {x : BHist}, Code x -> UnaryHistory x
  delta_symm : forall {x y : BHist}, delta x y = delta y x
  delta_triangle : forall {x y z : BHist}, delta x z <= delta x y + delta y z
  minimum_distance : forall {x y : BHist}, Code x -> Code y -> delta x y < d -> rho x y

theorem ErrorCode_unique_decoding_radius (C : ErrorCodeMinimumDistanceDecoding)
    {c1 c2 r : BHist} :
    C.Code c1 -> C.Code c2 -> C.delta c1 r <= C.t -> C.delta c2 r <= C.t ->
      C.rho c1 c2 ∧ UnaryHistory c1 ∧ UnaryHistory c2 := by
  intro codeC1 codeC2 c1Near c2Near
  have belowDistance : C.delta c1 c2 < C.d := by
    calc
      C.delta c1 c2 <= C.delta c1 r + C.delta r c2 := C.delta_triangle
      _ = C.delta c1 r + C.delta c2 r :=
        congrArg (fun h => C.delta c1 r + h) (C.delta_symm (x := r) (y := c2))
      _ <= C.t + C.t := Nat.add_le_add c1Near c2Near
      _ < C.d := C.radius_bound
  exact And.intro (C.minimum_distance codeC1 codeC2 belowDistance)
    (And.intro (C.code_unary codeC1) (C.code_unary codeC2))

end BEDC.Derived.ErrorCodeUp

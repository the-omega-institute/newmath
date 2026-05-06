import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatConstStream_certified_observation_determinacy {d m n : BHist} :
    UnaryHistory m -> UnaryHistory n -> hsame (RatConstStream d m) (RatConstStream d n) := by
  intro mUnary nUnary
  have pointSame := (RatStreamName_constant_witness (d := d) (e := d)).left
  exact hsame_trans (pointSame m mUnary) (hsame_symm (pointSame n nUnary))

end BEDC.Derived.StreamNameUp

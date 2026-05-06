import BEDC.FKernel.Hist
import BEDC.FKernel.Cont

namespace BEDC.Derived.RandomVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RandomVarPreimage_disjoint_binary_union_exactness
    {B C U_T A_B A_C A_U U_S : BHist} :
    hsame A_B B -> hsame A_C C -> hsame A_U U_T -> Cont B C U_T ->
      Cont A_B A_C U_S -> (hsame B C -> False) ->
        hsame A_U U_S ∧ (hsame A_B A_C -> False) := by
  intro samePreimageB samePreimageC samePreimageUnion targetUnion sourceUnion targetDisjoint
  have transportedUnion : hsame U_T U_S :=
    cont_respects_hsame (hsame_symm samePreimageB) (hsame_symm samePreimageC)
      targetUnion sourceUnion
  have sourceDisjoint : hsame A_B A_C -> False := by
    intro sameSource
    exact targetDisjoint
      (hsame_trans (hsame_symm samePreimageB) (hsame_trans sameSource samePreimageC))
  exact And.intro (hsame_trans samePreimageUnion transportedUnion) sourceDisjoint

end BEDC.Derived.RandomVarUp

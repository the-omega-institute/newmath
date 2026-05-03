import BEDC.Derived.MagmaUp

namespace BEDC.Derived.SemigroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem concrete_unary_history_semigroup_cont_assoc_classifier {h k l hk kl left right : BHist} :
    UnaryHistory h -> UnaryHistory k -> UnaryHistory l ->
      Cont h k hk -> Cont hk l left -> Cont k l kl -> Cont h kl right ->
        (UnaryHistory left ∧ UnaryHistory right ∧ hsame left right) := by
  intro unaryH unaryK unaryL hhk hleft hkl hright
  have unaryHK : UnaryHistory hk :=
    unary_cont_closed unaryH unaryK hhk
  have unaryLeft : UnaryHistory left :=
    unary_cont_closed unaryHK unaryL hleft
  have unaryKL : UnaryHistory kl :=
    unary_cont_closed unaryK unaryL hkl
  have unaryRight : UnaryHistory right :=
    unary_cont_closed unaryH unaryKL hright
  exact And.intro unaryLeft
    (And.intro unaryRight (cont_assoc_hsame hhk hleft hkl hright))

end BEDC.Derived.SemigroupUp

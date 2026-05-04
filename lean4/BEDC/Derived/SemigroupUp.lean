import BEDC.Derived.MagmaUp

namespace BEDC.Derived.SemigroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

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

theorem ConcreteUnaryHistorySemigroup_semanticNameCert :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (∀ {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (append h k) ∧ Cont h k (append h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') ∧
      (∀ {h k l hk kl left right : BHist}, Carrier h -> Carrier k -> Carrier l ->
        Cont h k hk -> Cont hk l left -> Cont k l kl -> Cont h kl right ->
          Classifier left right) := by
  dsimp
  constructor
  · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.left
  · constructor
    · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.right.left
    · constructor
      · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.right.right
      · intro h k l hk kl left right
        exact concrete_unary_history_semigroup_cont_assoc_classifier

end BEDC.Derived.SemigroupUp

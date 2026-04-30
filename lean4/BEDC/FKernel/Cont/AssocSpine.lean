import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_assoc_spine_symmetric_witnesses {a b c ab bc : BHist} :
    Cont a b ab -> Cont b c bc ->
      exists left : BHist, exists right : BHist,
        Cont ab c left /\ Cont a bc right /\ hsame left right /\ hsame right left := by
  intro hab hbc
  cases hab
  cases hbc
  exact ⟨append (append a b) c, append a (append b c), rfl, rfl,
    append_assoc a b c, hsame_symm (append_assoc a b c)⟩

theorem continuation_associativity_spine {h k l u v w z : BHist} :
    Cont h k u -> Cont u l v -> Cont k l w -> Cont h w z -> hsame v z := by
  exact cont_assoc_relational

end BEDC.FKernel.Cont

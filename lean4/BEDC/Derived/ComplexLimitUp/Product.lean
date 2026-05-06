import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexPointwiseProduct (s t : BHist -> BHist) (n : BHist) : BHist :=
  append (s n) (t n)

theorem ComplexLimit_pointwise_product_witness_package {s t N M : BHist -> BHist}
    {z w : BHist} :
    ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (ComplexPointwiseProduct s t) N (append z w) M ∧
        (forall {k n : BHist}, UnaryHistory k -> UnaryHistory n -> Cont (M k) n n ->
          exists ds : BHist, exists dt : BHist,
            ComplexDistance (s n) z ds ∧ ComplexDistance (t n) w dt ∧
              ComplexDistance (append (s n) (t n)) (append z w)
                (append (append (s n) (t n)) (append z w))) := by
  intro limitS limitT
  have productLimit :
      ComplexLimit (ComplexPointwiseProduct s t) N (append z w) M :=
    ComplexLimit_pointwise_append_same_modulus_closed limitS limitT
  constructor
  · exact productLimit
  · intro k n unaryK unaryN controlled
    cases limitS with
    | intro _regularS restS =>
        cases restS with
        | intro carrierZ modulusS =>
            cases limitT with
            | intro _regularT restT =>
                cases restT with
                | intro carrierW modulusT =>
                    cases modulusS k n unaryK unaryN controlled with
                    | intro ds distanceS =>
                        cases modulusT k n unaryK unaryN controlled with
                        | intro dt distanceT =>
                            have leftUnary : UnaryHistory (append (s n) (t n)) :=
                              unary_append_closed distanceS.left distanceT.left
                            have rightUnary : UnaryHistory (append z w) :=
                              unary_append_closed
                                (ComplexHistoryCarrier_unary carrierZ)
                                (ComplexHistoryCarrier_unary carrierW)
                            exact Exists.intro ds
                              (Exists.intro dt
                                (And.intro distanceS
                                  (And.intro distanceT
                                    (And.intro leftUnary
                                      (And.intro rightUnary
                                        (And.intro (unary_append_closed leftUnary rightUnary)
                                          (Or.inl (cont_intro rfl))))))))

end BEDC.Derived.ComplexLimitUp

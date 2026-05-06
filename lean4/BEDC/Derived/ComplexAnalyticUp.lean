import BEDC.Derived.ComplexUp
import BEDC.Derived.ComplexDiffUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.ComplexAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

theorem ComplexAnalytic_component_continuation_witness {real imag z q zq : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> Cont real imag z -> UnaryHistory q ->
      Cont z q zq -> ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ Cont imag q imagq ∧ Cont real imagq zq ∧
          PositiveUnaryDenominator imagq := by
  intro _realCarrier imagCarrier realImag qUnary zqCont
  cases cont_assoc_middle_exists realImag zqCont with
  | intro imagq split =>
      have imagqCarrier : RatHistoryCarrier imagq :=
        RatHistoryCarrier_hsame_transport split.left.symm
          (RatHistoryCarrier_append_unary_denominator_closed imagCarrier qUnary)
      exact ⟨imagq, imagqCarrier, split.left, split.right,
        RatHistoryCarrier_iff_positive_denominator.mp imagqCarrier⟩

theorem ComplexAnalytic_component_continuation_complex_carrier {real imag z : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> Cont real imag z ->
      ComplexHistoryCarrier z := by
  intro realCarrier imagCarrier realImag
  exact ProdHistoryCarrier_cont_intro realCarrier imagCarrier realImag

def CplxExp (z w : BHist) : Prop :=
  ∃ real imag realOut imagOut : BHist,
    RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧ Cont real imag z ∧
      RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w ∧
        hsame realOut (append real imag) ∧ hsame imagOut (append imag real)

theorem CplxExp_component_carrier_witness {z w : BHist} :
    CplxExp z w -> ComplexHistoryCarrier z ∧ ComplexHistoryCarrier w := by
  intro expWitness
  cases expWitness with
  | intro real realData =>
      cases realData with
      | intro imag imagData =>
          cases imagData with
          | intro realOut realOutData =>
              cases realOutData with
              | intro imagOut componentData =>
                  exact And.intro
                    (ProdHistoryCarrier_cont_intro componentData.left
                      componentData.right.left componentData.right.right.left)
                    (ProdHistoryCarrier_cont_intro componentData.right.right.right.left
                      componentData.right.right.right.right.left
                      componentData.right.right.right.right.right.left)

theorem CplxExp_component_well_defined
    {real imag realOut imagOut z z' w w' : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> RatHistoryCarrier realOut ->
      RatHistoryCarrier imagOut -> Cont real imag z -> Cont real imag z' ->
        Cont realOut imagOut w -> Cont realOut imagOut w' ->
          hsame realOut (append real imag) -> hsame imagOut (append imag real) ->
            CplxExp z w ∧ CplxExp z' w' ∧
              ComplexHistoryClassifier z z' ∧ ComplexHistoryClassifier w w' := by
  intro realCarrier imagCarrier realOutCarrier imagOutCarrier contZ contZ' contW contW'
    sameRealOut sameImagOut
  have expZW : CplxExp z w :=
    Exists.intro real
      (Exists.intro imag
        (Exists.intro realOut
          (Exists.intro imagOut
            (And.intro realCarrier
              (And.intro imagCarrier
                (And.intro contZ
                  (And.intro realOutCarrier
                    (And.intro imagOutCarrier
                      (And.intro contW (And.intro sameRealOut sameImagOut))))))))))
  have expZ'W' : CplxExp z' w' :=
    Exists.intro real
      (Exists.intro imag
        (Exists.intro realOut
          (Exists.intro imagOut
            (And.intro realCarrier
              (And.intro imagCarrier
                (And.intro contZ'
                  (And.intro realOutCarrier
                    (And.intro imagOutCarrier
                      (And.intro contW' (And.intro sameRealOut sameImagOut))))))))))
  have realClassifier : RatHistoryClassifier real real :=
    And.intro realCarrier (And.intro realCarrier (hsame_refl real))
  have imagClassifier : RatHistoryClassifier imag imag :=
    And.intro imagCarrier (And.intro imagCarrier (hsame_refl imag))
  have realOutClassifier : RatHistoryClassifier realOut realOut :=
    And.intro realOutCarrier (And.intro realOutCarrier (hsame_refl realOut))
  have imagOutClassifier : RatHistoryClassifier imagOut imagOut :=
    And.intro imagOutCarrier (And.intro imagOutCarrier (hsame_refl imagOut))
  exact And.intro expZW
    (And.intro expZ'W'
      (And.intro
        (ComplexHistoryClassifier_component_classifier_intro realClassifier imagClassifier
          contZ contZ')
        (ComplexHistoryClassifier_component_classifier_intro realOutClassifier imagOutClassifier
          contW contW')))

theorem CplxExp_output_hsame_transport {z w w' : BHist} :
    CplxExp z w -> hsame w w' -> ComplexHistoryCarrier w' ->
      exists real imag realOut imagOut : BHist,
        RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧ Cont real imag z ∧
          RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w' ∧
            hsame realOut (append real imag) ∧ hsame imagOut (append imag real) := by
  intro expWitness sameWW' _carrierW'
  cases expWitness with
  | intro real expRest =>
      cases expRest with
      | intro imag expRest =>
          cases expRest with
          | intro realOut expRest =>
              cases expRest with
              | intro imagOut data =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (Exists.intro realOut
                        (Exists.intro imagOut
                          (And.intro data.left
                            (And.intro data.right.left
                              (And.intro data.right.right.left
                                (And.intro data.right.right.right.left
                                  (And.intro data.right.right.right.right.left
                                    (And.intro
                                      (cont_result_hsame_transport
                                        data.right.right.right.right.right.left sameWW')
                                      (And.intro data.right.right.right.right.right.right.left
                                        data.right.right.right.right.right.right.right))))))))))

def CplxPureImaginary (theta z : BHist) : Prop :=
  UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta))

theorem CplxExp_pure_imaginary_component_witness {theta z w : BHist} :
    CplxPureImaginary theta z -> CplxExp z w ->
      exists real imag realOut imagOut : BHist,
        RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧ Cont real imag z ∧
        RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w ∧
            hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) ∧
              hsame realOut (append real imag) ∧ hsame imagOut (append imag real) := by
  intro pureImaginary expWitness
  cases expWitness with
  | intro real expRest =>
      cases expRest with
      | intro imag expRest =>
          cases expRest with
          | intro realOut expRest =>
              cases expRest with
              | intro imagOut data =>
                  exact ⟨real, imag, realOut, imagOut, data.left, data.right.left,
                    data.right.right.left, data.right.right.right.left,
                    data.right.right.right.right.left,
                    data.right.right.right.right.right.left, pureImaginary.right,
                    data.right.right.right.right.right.right.left,
                    data.right.right.right.right.right.right.right⟩

theorem CplxExp_pure_imaginary_euler_component_witness {theta z w : BHist} :
    CplxPureImaginary theta z -> CplxExp z w ->
      ∃ real imag realOut imagOut : BHist,
        RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧ Cont real imag z ∧
          RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w ∧
            hsame realOut z ∧ hsame imagOut (append imag real) ∧
              hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
  intro pureImaginary expWitness
  cases expWitness with
  | intro real expRest =>
      cases expRest with
      | intro imag expRest =>
          cases expRest with
          | intro realOut expRest =>
              cases expRest with
              | intro imagOut data =>
                  have sameRealOutZ : hsame realOut z :=
                    hsame_trans data.right.right.right.right.right.right.left
                      (hsame_symm data.right.right.left)
                  exact Exists.intro real
                    (Exists.intro imag
                      (Exists.intro realOut
                        (Exists.intro imagOut
                          (And.intro data.left
                            (And.intro data.right.left
                              (And.intro data.right.right.left
                                (And.intro data.right.right.right.left
                                  (And.intro data.right.right.right.right.left
                                    (And.intro data.right.right.right.right.right.left
                                      (And.intro sameRealOutZ
                                        (And.intro
                                          data.right.right.right.right.right.right.right
                                          pureImaginary.right)))))))))))

def CplxPower (a s w : BHist) : Prop :=
  ComplexHistoryCarrier a ∧ ComplexHistoryCarrier s ∧ ComplexHistoryCarrier w ∧
    hsame w (append s a)

theorem CplxPower_dirichlet_factor_witness {n s : BHist} :
    UnaryHistory n -> ComplexHistoryCarrier s ->
      CplxPower (append (BHist.e1 n) (BHist.e1 BHist.Empty)) s
          (append s (append (BHist.e1 n) (BHist.e1 BHist.Empty))) ∧
        ComplexHistoryCarrier (append s (append (BHist.e1 n) (BHist.e1 BHist.Empty))) := by
  intro nUnary sCarrier
  have realCarrier : RatHistoryCarrier (BHist.e1 n) := by
    exact RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr nUnary)
  have imagCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
    exact RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
  have factorCarrier :
      ComplexHistoryCarrier (append (BHist.e1 n) (BHist.e1 BHist.Empty)) :=
    ProdHistoryCarrier_append_intro realCarrier imagCarrier
  have resultCarrier :
      ComplexHistoryCarrier (append s (append (BHist.e1 n) (BHist.e1 BHist.Empty))) :=
    ComplexHistoryCarrier_append_unary_closed sCarrier
      (unary_append_closed (unary_e1_closed nUnary) (unary_e1_closed unary_empty))
  exact And.intro
    (And.intro factorCarrier
      (And.intro sCarrier (And.intro resultCarrier (hsame_refl _))))
    resultCarrier

theorem CplxPower_dirichlet_factor_classifier {a s w : BHist} :
    CplxPower a s w -> ComplexHistoryClassifier w (append s a) ∧ hsame w (append s a) := by
  intro power
  have aUnary : UnaryHistory a := ComplexHistoryCarrier_unary power.left
  have targetCarrier : ComplexHistoryCarrier (append s a) :=
    ComplexHistoryCarrier_append_unary_closed power.right.left aUnary
  exact And.intro
    (And.intro power.right.right.left
      (And.intro targetCarrier power.right.right.right))
    power.right.right.right

def CplxModArg (z r theta : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ CplxNonZero z ∧ UnaryHistory r ∧ UnaryHistory theta ∧
    ComplexHistoryClassifier z (append (BHist.e1 r) (BHist.e1 theta))

def CplxLog (realLog : BHist -> BHist) (z w : BHist) : Prop :=
  ∃ r theta logR : BHist,
    CplxModArg z r theta ∧ hsame logR (realLog r) ∧ Cont logR theta w ∧
      ComplexHistoryCarrier w

theorem CplxLog_exp_inverse_carrier_witness
    {realLog : BHist -> BHist} {z w expw : BHist} :
    CplxLog realLog z w -> CplxExp w expw ->
      ComplexHistoryCarrier z ∧ ComplexHistoryCarrier w ∧ ComplexHistoryCarrier expw ∧
        exists r theta logR : BHist,
          CplxModArg z r theta ∧ hsame logR (realLog r) ∧ Cont logR theta w := by
  intro logWitness expWitness
  have expCarriers := CplxExp_component_carrier_witness expWitness
  cases logWitness with
  | intro r logRest =>
      cases logRest with
      | intro theta logRest =>
          cases logRest with
          | intro logR logData =>
              exact And.intro logData.left.left
                (And.intro expCarriers.left
                  (And.intro expCarriers.right
                    (Exists.intro r
                      (Exists.intro theta
                        (Exists.intro logR
                          (And.intro logData.left
                            (And.intro logData.right.left logData.right.right.left)))))))

theorem CplxPureImaginary_e1_tail_iff {theta tail : BHist} :
    CplxPureImaginary theta (BHist.e1 tail) <->
      UnaryHistory theta /\ hsame tail (append (BHist.e1 BHist.Empty) theta) := by
  constructor
  · intro pureImaginary
    exact And.intro pureImaginary.left (hsame_e1_iff.mp pureImaginary.right)
  · intro tailData
    exact And.intro tailData.left (hsame_e1_congr tailData.right)

theorem CplxPureImaginary_component_deterministic {theta theta' z : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary theta' z ->
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 theta')) ∧ hsame theta theta' := by
  intro left right
  have sameComponents :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 theta')) :=
    hsame_trans (hsame_symm left.right) right.right
  have sameImaginaryE1 : hsame (BHist.e1 theta) (BHist.e1 theta') :=
    append_left_cancel (h := BHist.e1 BHist.Empty) sameComponents
  exact And.intro sameComponents (hsame_e1_iff.mp sameImaginaryE1)

theorem CplxPureImaginary_complex_carrier_witness {theta z : BHist} :
    CplxPureImaginary theta z ->
      UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) ∧
        ComplexHistoryCarrier z := by
  intro pureImaginary
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
      have pureCarrier :
          ComplexHistoryCarrier (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
        exact ProdHistoryCarrier_append_intro realCarrier imagCarrier
      exact And.intro thetaUnary
        (And.intro sameZ
          (ProdHistoryCarrier_hsame_transport (hsame_symm sameZ) pureCarrier))

theorem CplxExp_euler_pure_imaginary_carrier_witness {theta z w : BHist} :
    CplxPureImaginary theta z -> CplxExp z w ->
      UnaryHistory theta ∧ ComplexHistoryCarrier z ∧ ComplexHistoryCarrier w := by
  intro pureImaginary expWitness
  have pureCarrier := CplxPureImaginary_complex_carrier_witness pureImaginary
  have expCarriers := CplxExp_component_carrier_witness expWitness
  exact And.intro pureCarrier.left (And.intro expCarriers.left expCarriers.right)

theorem CplxExp_pure_imaginary_source_witness {theta : BHist} :
    UnaryHistory theta ->
      CplxExp (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
          (append (BHist.e1 theta) (BHist.e1 BHist.Empty))) ∧
        CplxPureImaginary theta (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
  intro thetaUnary
  have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
    exact RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
  have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
    exact RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
  have realOutCarrier :
      RatHistoryCarrier (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
    exact RatHistoryCarrier_append_unary_denominator_closed realCarrier
      (unary_e1_closed thetaUnary)
  have imagOutCarrier :
      RatHistoryCarrier (append (BHist.e1 theta) (BHist.e1 BHist.Empty)) := by
    exact RatHistoryCarrier_append_unary_denominator_closed imagCarrier
      (unary_e1_closed unary_empty)
  have expWitness :
      CplxExp (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
          (append (BHist.e1 theta) (BHist.e1 BHist.Empty))) :=
    Exists.intro (BHist.e1 BHist.Empty)
      (Exists.intro (BHist.e1 theta)
        (Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
          (Exists.intro (append (BHist.e1 theta) (BHist.e1 BHist.Empty))
            (And.intro realCarrier
              (And.intro imagCarrier
                (And.intro (cont_intro rfl)
                  (And.intro realOutCarrier
                    (And.intro imagOutCarrier
                      (And.intro (cont_intro rfl)
                          (And.intro (hsame_refl _)
                            (hsame_refl _)))))))))))
  exact And.intro expWitness (And.intro thetaUnary (hsame_refl _))

theorem CplxPureImaginary_hsame_transport_witness {theta z z' : BHist} :
    hsame z z' -> CplxPureImaginary theta z ->
      CplxPureImaginary theta z' ∧ hsame z' (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
  intro sameZZ' pureImaginary
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have sameZ' : hsame z' (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) :=
        hsame_trans (hsame_symm sameZZ') sameZ
      exact And.intro (And.intro thetaUnary sameZ') sameZ'

theorem CplxPureImaginary_name_certificate :
    NameCert (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      hsame := by
  constructor
  · exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
      (Exists.intro BHist.Empty
        (And.intro unary_empty (hsame_refl _)))
  · intro z _source
    exact hsame_refl z
  · intro z z' sameZZ'
    exact hsame_symm sameZZ'
  · intro z z' z'' sameZZ' sameZ'Z''
    exact hsame_trans sameZZ' sameZ'Z''
  · intro z z' sameZZ' source
    cases source with
    | intro theta pureImaginary =>
        exact Exists.intro theta
          (CplxPureImaginary_hsame_transport_witness sameZZ' pureImaginary).left

theorem CplxPureImaginary_phase_stability_witness {theta phi z : BHist} :
    CplxPureImaginary theta z -> hsame theta phi ->
      CplxPureImaginary phi z ∧ UnaryHistory phi ∧
        hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
  intro pureImaginary sameThetaPhi
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have phiUnary : UnaryHistory phi := unary_transport thetaUnary sameThetaPhi
      have sameZPhi : hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
        cases sameThetaPhi
        exact sameZ
      exact And.intro (And.intro phiUnary sameZPhi) (And.intro phiUnary sameZPhi)

theorem CplxPureImaginary_empty_absurd {theta : BHist} :
    CplxPureImaginary theta BHist.Empty -> False := by
  intro pureImaginary
  exact ComplexHistoryCarrier_not_empty
    (CplxPureImaginary_complex_carrier_witness pureImaginary).right.right (hsame_refl BHist.Empty)

theorem CplxPureImaginary_empty_continuation_absurd {theta z q : BHist} :
    CplxPureImaginary theta z -> Cont z q BHist.Empty -> False := by
  intro pureImaginary emptyCont
  have sourceEmpty : hsame z BHist.Empty := (append_eq_empty_iff.mp emptyCont.symm).left
  exact CplxPureImaginary_empty_absurd
    (CplxPureImaginary_hsame_transport_witness sourceEmpty pureImaginary).left

theorem CplxPureImaginary_component_continuation_witness {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ Cont (BHist.e1 theta) q imagq ∧
          Cont (BHist.e1 BHist.Empty) imagq zq ∧ PositiveUnaryDenominator imagq := by
  intro pureImaginary qUnary zqCont
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
      exact
        ComplexAnalytic_component_continuation_witness realCarrier imagCarrier sameZ qUnary zqCont

theorem CplxPureImaginary_suffix_component_tail_witness {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ hsame imagq (BHist.e1 (append theta q)) ∧
          Cont (BHist.e1 BHist.Empty) imagq zq ∧ PositiveUnaryDenominator imagq := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq data =>
      have sameTail : hsame imagq (BHist.e1 (append theta q)) :=
        data.right.left.trans (unary_append_e1_left (h := q) (k := theta) qUnary)
      exact ⟨imagq, data.left, sameTail, data.right.right.left, data.right.right.right⟩

theorem CplxPureImaginary_suffix_parameter_readback {theta psi z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      CplxPureImaginary psi zq -> hsame psi (append theta q) := by
  intro pureTheta qUnary zqCont purePsi
  cases CplxPureImaginary_suffix_component_tail_witness pureTheta qUnary zqCont with
  | intro imagq data =>
      have displayedCont :
          Cont (BHist.e1 BHist.Empty) imagq
            (append (BHist.e1 BHist.Empty) (BHist.e1 psi)) :=
        cont_result_hsame_transport data.right.right.left purePsi.right
      have sameImaginaryDisplay : hsame (BHist.e1 psi) imagq :=
        append_left_cancel (h := BHist.e1 BHist.Empty) displayedCont
      exact hsame_e1_iff.mp (hsame_trans sameImaginaryDisplay data.right.left)

theorem CplxPureImaginary_suffix_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq ∧ (hsame zq BHist.Empty -> False) := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq split =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have zqCarrier : ComplexHistoryCarrier zq :=
        ComplexAnalytic_component_continuation_complex_carrier realCarrier split.left
          split.right.right.left
      exact And.intro zqCarrier (ComplexHistoryCarrier_not_empty zqCarrier)

theorem CplxPureImaginary_suffix_continuation_classifier {theta phi z w q q' zq wq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> hsame theta phi ->
      UnaryHistory q -> hsame q q' -> Cont z q zq -> Cont w q' wq ->
        ComplexHistoryClassifier zq wq := by
  intro pureTheta purePhi sameThetaPhi qUnary sameQQ' contZ contW
  cases CplxPureImaginary_component_continuation_witness pureTheta qUnary contZ with
  | intro imagq leftData =>
      have qUnary' : UnaryHistory q' := unary_transport qUnary sameQQ'
      cases CplxPureImaginary_component_continuation_witness purePhi qUnary' contW with
      | intro imagq' rightData =>
          have thetaUnary : UnaryHistory theta := pureTheta.left
          have phiUnary : UnaryHistory phi := purePhi.left
          have realClassifier :
              RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
            RatHistoryClassifier_e1_tail_unary_iff.mpr
              ⟨unary_empty, unary_empty, hsame_refl BHist.Empty⟩
          have baseImagClassifier :
              RatHistoryClassifier (BHist.e1 theta) (BHist.e1 phi) :=
            RatHistoryClassifier_e1_tail_unary_iff.mpr
              ⟨thetaUnary, phiUnary, sameThetaPhi⟩
          have continuedImagClassifier :
              RatHistoryClassifier (append (BHist.e1 theta) q) (append (BHist.e1 phi) q') :=
            RatHistoryClassifier_append_unary_denominator_closed baseImagClassifier qUnary
              sameQQ'
          have imagClassifier : RatHistoryClassifier imagq imagq' :=
            RatHistoryClassifier_hsame_transport leftData.right.left.symm
              rightData.right.left.symm continuedImagClassifier
          exact ComplexHistoryClassifier_component_classifier_intro realClassifier imagClassifier
            leftData.right.right.left rightData.right.right.left

theorem CplxPureImaginary_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq data =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      exact ProdHistoryCarrier_cont_intro realCarrier data.left data.right.right.left

theorem CplxPureImaginary_component_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq := by
  exact CplxPureImaginary_continuation_complex_carrier

theorem CplxPureImaginary_continuation_e0_result_absurd {theta z q tail : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q (BHist.e0 tail) -> False := by
  intro pureImaginary qUnary zqCont
  have resultCarrier : ComplexHistoryCarrier (BHist.e0 tail) :=
    CplxPureImaginary_continuation_complex_carrier pureImaginary qUnary zqCont
  exact unary_no_zero_extension (ComplexHistoryCarrier_unary resultCarrier)

theorem CplxExp_pure_imaginary_euler_component_package {theta z w : BHist} :
    CplxPureImaginary theta z -> CplxExp z w ->
      ∃ realOut imagOut : BHist,
        RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w ∧
          hsame realOut (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) ∧
            hsame imagOut (append (BHist.e1 theta) (BHist.e1 BHist.Empty)) ∧
              ComplexHistoryCarrier w := by
  intro pureImaginary expWitness
  cases expWitness with
  | intro real expRest =>
      cases expRest with
      | intro imag expRest =>
          cases expRest with
          | intro realOut expRest =>
              cases expRest with
              | intro imagOut data =>
                  have realUnary : UnaryHistory real :=
                    (PositiveUnaryDenominator_unary_and_nonempty
                      (RatHistoryCarrier_iff_positive_denominator.mp data.left)).left
                  have imagUnary : UnaryHistory imag :=
                    (PositiveUnaryDenominator_unary_and_nonempty
                      (RatHistoryCarrier_iff_positive_denominator.mp data.right.left)).left
                  have sameInput :
                      hsame (append real imag)
                        (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) :=
                    data.right.right.left.symm.trans pureImaginary.right
                  have sameRealOut :
                      hsame realOut (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
                    exact data.right.right.right.right.right.right.left.trans sameInput
                  have sameImagOut :
                      hsame imagOut (append (BHist.e1 theta) (BHist.e1 BHist.Empty)) := by
                    exact hsame_trans data.right.right.right.right.right.right.right
                      (hsame_trans (unary_append_comm_hsame imagUnary realUnary)
                        (hsame_trans sameInput
                          (unary_append_comm_hsame (unary_e1_closed unary_empty)
                            (unary_e1_closed pureImaginary.left))))
                  have outputCarrier : ComplexHistoryCarrier w :=
                    ProdHistoryCarrier_cont_intro data.right.right.right.left
                      data.right.right.right.right.left data.right.right.right.right.right.left
                  exact ⟨realOut, imagOut, data.right.right.right.left,
                    data.right.right.right.right.left, data.right.right.right.right.right.left,
                    sameRealOut, sameImagOut, outputCarrier⟩

def CplxSinCos (z s c : BHist) : Prop :=
  ∃ iz negIz expIz expNegIz : BHist,
    ComplexHistoryCarrier z ∧ CplxExp iz expIz ∧ CplxExp negIz expNegIz ∧
      hsame s (append expIz expNegIz) ∧ hsame c (append expIz expIz)

theorem CplxPureImaginary_witness_unique {theta phi z : BHist} :
    (UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta))) ->
      (UnaryHistory phi ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi))) ->
        hsame theta phi := by
  intro left right
  have sameAnchors :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) :=
    hsame_trans (hsame_symm left.right) right.right
  exact hsame_e1_iff.mp (append_left_cancel (h := BHist.e1 BHist.Empty) sameAnchors)

theorem CplxPureImaginary_suffix_source_deterministic {theta phi z w q zq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> Cont z q zq ->
      Cont w q zq -> hsame theta phi := by
  intro pureTheta purePhi zCont wCont
  have sameZW : hsame z w := cont_right_cancel zCont wCont
  have purePhiAtZ : CplxPureImaginary phi z :=
    (CplxPureImaginary_hsame_transport_witness (hsame_symm sameZW) purePhi).left
  exact CplxPureImaginary_witness_unique pureTheta purePhiAtZ

theorem CplxPureImaginary_suffix_tail_deterministic {theta phi z w q q' zq wq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> hsame theta phi ->
      Cont z q zq -> Cont w q' wq -> hsame zq wq -> hsame q q' := by
  intro pureTheta purePhi sameThetaPhi zCont wCont sameResult
  have sameAnchors :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
    cases sameThetaPhi
    rfl
  have sameZW : hsame z w :=
    hsame_trans pureTheta.right (hsame_trans sameAnchors (hsame_symm purePhi.right))
  cases sameZW
  exact append_left_cancel (h := z) (zCont.symm.trans (sameResult.trans wCont))

theorem complex_analytic_licensed_not_primitive :
    SemanticNameCert
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z z' : BHist =>
        (exists theta : BHist, CplxPureImaginary theta z) ∧
          (exists theta : BHist, CplxPureImaginary theta z') ∧ hsame z z') := by
  exact {
    core := {
      carrier_inhabited :=
        BEDC.FKernel.NameCert.NameCert.carrier_inhabited CplxPureImaginary_name_certificate
      equiv_refl := by
        intro z source
        exact And.intro source (And.intro source (hsame_refl z))
      equiv_symm := by
        intro z z' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro z z' z'' leftClass rightClass
        exact And.intro leftClass.left
          (And.intro rightClass.right.left
            (hsame_trans leftClass.right.right rightClass.right.right))
      carrier_respects_equiv := by
        intro z z' classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro z source
      exact source
    ledger_sound := by
      intro z source
      exact source
  }

end BEDC.Derived.ComplexAnalyticUp

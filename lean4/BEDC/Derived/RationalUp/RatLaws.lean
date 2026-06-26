import BEDC.Derived.RationalUp.IntLaws

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp

theorem intOfNat_nonzero_of_den (x : RatNum) :
    IntNonzero (intOfNat x.den (ratDenCarrier x)) := by
  unfold IntNonzero intApart0 intOfNat
  exact x.den_pos

theorem RatEq_trans (x y z : RatNum) :
    RatEq x y -> RatEq y z -> RatEq x z := by
  intro hxy hyz
  unfold RatEq at hxy hyz ⊢
  let yd := intOfNat y.den (ratDenCarrier y)
  let xd := intOfNat x.den (ratDenCarrier x)
  let zd := intOfNat z.den (ratDenCarrier z)
  have ydNZ : IntNonzero yd := by
    unfold yd
    exact intOfNat_nonzero_of_den y
  have hxyInt : IntEq (IntMul x.num yd) (IntMul y.num xd) := by
    unfold IntEq IntMul yd xd
    exact hxy
  have hyzInt : IntEq (IntMul y.num zd) (IntMul z.num yd) := by
    unfold IntEq IntMul yd zd
    exact hyz
  apply IntMul_left_cancel (c := yd)
  · exact ydNZ
  · exact IntEq_trans (intMul_rotate_left yd x.num zd)
      (IntEq_trans (intMul_right_congr hxyInt)
        (IntEq_trans (intMul_middle_swap y.num xd zd)
          (IntEq_trans (intMul_right_congr hyzInt)
            (IntEq_symm (intMul_rotate_left yd z.num xd)))))

theorem intOfNat_hsame_congr {a b : BHist} (ha : UnaryHistory a) (hb : UnaryHistory b) :
    hsame a b -> IntEq (intOfNat a ha) (intOfNat b hb) := by
  intro same
  unfold IntEq intOfNat intToPair
  apply IntPairClassifier_of_length_eq ⟨ha, unary_empty⟩ ⟨hb, unary_empty⟩
  change BEDC.FKernel.ExternalBinary.bwordLength a +
      BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty =
    BEDC.FKernel.ExternalBinary.bwordLength b +
      BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  exact (NatUp_unary_standard_bridge.right.right.right.left ha hb).mp same

theorem intOfNat_natMul_comm (a b : BHist) (ha : UnaryHistory a) (hb : UnaryHistory b) :
    IntEq (intOfNat (natMulFn a b) (natMulFn_unary ha hb))
      (intOfNat (natMulFn b a) (natMulFn_unary hb ha)) := by
  exact intOfNat_hsame_congr (natMulFn_unary ha hb) (natMulFn_unary hb ha)
    (NatMul_comm_hsame ha hb (natMulFn_rel ha hb) (natMulFn_rel hb ha))

theorem ratInvApart_mul (x : RatNum) (hx : ratApart0 x) :
    RatEq (ratMul x (ratInvApart x hx)) ratOne := by
  unfold RatEq ratMul ratInvApart ratOne intToRat
  cases x with
  | mk num den den_pos =>
      cases num with
      | mk sign mag carrier =>
          let denUnary :=
            ratDenCarrier
              { num := { sign := sign, magnitude := mag, carrier := carrier },
                den := den,
                den_pos := den_pos }
          let magUnary := carrier.right
          have numeratorNat :
              IntEq
                (IntMul { sign := sign, magnitude := mag, carrier := carrier }
                  (intOfNatWithSign sign den denUnary))
                (intOfNat (natMulFn mag den) (natMulFn_unary magUnary denUnary)) := by
            exact intMul_same_sign_nat sign mag den magUnary denUnary
          have targetDen :
              IntEq
                (intOfNat (natMulFn mag den) (natMulFn_unary magUnary denUnary))
                (intOfNat (natMulFn den mag) (natMulFn_unary denUnary magUnary)) :=
            intOfNat_natMul_comm mag den magUnary denUnary
          have numeratorEqDen :
              IntEq
                (IntMul { sign := sign, magnitude := mag, carrier := carrier }
                  (intOfNatWithSign sign den denUnary))
                (intOfNat (natMulFn den mag) (natMulFn_unary denUnary magUnary)) :=
            IntEq_trans numeratorNat targetDen
          exact IntEq_trans (intMul_one_right _)
            (IntEq_trans numeratorEqDen (IntEq_symm (intMul_one_left _)))

end BEDC.Derived.RationalUp

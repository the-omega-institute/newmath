import BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD
import BEDC.Derived.RHRoute.WeilPositivityRoute

namespace BEDC.Derived.RHRoute.WeilPrimeSensitivePacket

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.IntervalMatrixPSD
open BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD
open BEDC.Derived.RHRoute.WeilPositivityRoute

abbrev Rat : Type :=
  RatNum

def quad2 (b11 b12 b22 c1 c2 : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratMul b11 (ratMul c1 c1))
      (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
    (ratMul b22 (ratMul c2 c2))

def thetaQuad
    (a11 a12 a22 p11 p12 p22 theta c1 c2 : Rat) : Rat :=
  quad2
    (ratAdd a11 (ratMul theta p11))
    (ratAdd a12 (ratMul theta p12))
    (ratAdd a22 (ratMul theta p22))
    c1 c2

structure PrimeSensitive2x2Cert where
  a11 : Rat
  a12 : Rat
  a22 : Rat
  p11 : Rat
  p12 : Rat
  p22 : Rat
  theta_minus : Rat
  theta_plus : Rat
  epsilon : Rat
  a01 : Rat
  a02 : Rat
  prime_source : WeilTermSource 2
  prime_source_readback :
    prime_source = WeilTermSource.primePower primeTwoPowerIndex
  p_nonzero : ratLt p11 ratZero
  theta_minus_lt_one : ratLt theta_minus ratOne
  one_lt_theta_plus : ratLt ratOne theta_plus
  epsilon_pos : ratLt ratZero epsilon
  cross_lower :
    ratLe epsilon
      (thetaQuad a11 a12 a22 p11 p12 p22 theta_minus a01 a02)
  cross_upper :
    ratLe
      (thetaQuad a11 a12 a22 p11 p12 p22 theta_plus a01 a02)
      (ratNeg epsilon)
  marginCert : Fixed2x2Cert

theorem finite_weil_packet_prime_sensitive
    (C : PrimeSensitive2x2Cert) :
    ratLt C.theta_minus ratOne ∧
      ratLt ratOne C.theta_plus ∧
        ratLt ratZero C.epsilon ∧
          ratLe C.epsilon
            (thetaQuad C.a11 C.a12 C.a22 C.p11 C.p12 C.p22
              C.theta_minus C.a01 C.a02) ∧
            ratLe
              (thetaQuad C.a11 C.a12 C.a22 C.p11 C.p12 C.p22
                C.theta_plus C.a01 C.a02)
              (ratNeg C.epsilon) :=
  ⟨C.theta_minus_lt_one,
    C.one_lt_theta_plus,
    C.epsilon_pos,
    C.cross_lower,
    C.cross_upper⟩

theorem finite_weil_packet_margin_psd
    (C : PrimeSensitive2x2Cert) (c1 c2 : Rat) :
    ratLe ratZero
      (quad2 C.marginCert.b11 C.marginCert.b12 C.marginCert.b22 c1 c2) := by
  exact fixed2x2_cert_psd C.marginCert c1 c2

private theorem zero_le_zero : ratLe ratZero ratZero := by
  exact ratLe_refl ratZero

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem zero_lt_one : ratLt ratZero ratOne := by
  exact ratLtBool_true_to_ratLt (by rfl)

private theorem one_lt_two : ratLt ratOne (natRat 2) := by
  exact ratLtBool_true_to_ratLt (by rfl)

private theorem neg_two_lt_zero : ratLt (ratNeg (natRat 2)) ratZero := by
  exact ratLtBool_true_to_ratLt (by rfl)

private theorem one_le_three :
    ratLe ratOne
      (thetaQuad (natRat 3) ratZero ratOne
        (ratNeg (natRat 2)) ratZero ratZero ratZero ratOne ratZero) := by
  exact ratLeBool_true_to_ratLe (by rfl)

private theorem neg_one_upper :
    ratLe
      (thetaQuad (natRat 3) ratZero ratOne
        (ratNeg (natRat 2)) ratZero ratZero (natRat 2) ratOne ratZero)
      (ratNeg ratOne) := by
  exact ratLeBool_true_to_ratLe (by rfl)

def canonicalPrimeSensitiveMarginCert : Fixed2x2Cert where
  lo11 := ratZero
  hi11 := ratZero
  lo12 := ratZero
  hi12 := ratZero
  lo22 := ratZero
  hi22 := ratZero
  b11 := ratZero
  b12 := ratZero
  b22 := ratZero
  hord11 := zero_le_zero
  hord12 := zero_le_zero
  hord22 := zero_le_zero
  hlo11Nonneg := zero_le_zero
  hlo22Nonneg := zero_le_zero
  hdetCert := zero_le_zero
  hb11lo := zero_le_zero
  hb11hi := zero_le_zero
  hb12lo := zero_le_zero
  hb12hi := zero_le_zero
  hb22lo := zero_le_zero
  hb22hi := zero_le_zero

def canonicalPrimeSensitiveCert : PrimeSensitive2x2Cert where
  a11 := natRat 3
  a12 := ratZero
  a22 := ratOne
  p11 := ratNeg (natRat 2)
  p12 := ratZero
  p22 := ratZero
  theta_minus := ratZero
  theta_plus := natRat 2
  epsilon := ratOne
  a01 := ratOne
  a02 := ratZero
  prime_source := WeilTermSource.primePower primeTwoPowerIndex
  prime_source_readback := rfl
  p_nonzero := neg_two_lt_zero
  theta_minus_lt_one := zero_lt_one
  one_lt_theta_plus := one_lt_two
  epsilon_pos := zero_lt_one
  cross_lower := one_le_three
  cross_upper := neg_one_upper
  marginCert := canonicalPrimeSensitiveMarginCert

theorem canonical_prime_sensitive :
    ratLt canonicalPrimeSensitiveCert.theta_minus ratOne ∧
      ratLt ratOne canonicalPrimeSensitiveCert.theta_plus ∧
        ratLt ratZero canonicalPrimeSensitiveCert.epsilon ∧
          ratLe canonicalPrimeSensitiveCert.epsilon
            (thetaQuad canonicalPrimeSensitiveCert.a11
              canonicalPrimeSensitiveCert.a12
              canonicalPrimeSensitiveCert.a22
              canonicalPrimeSensitiveCert.p11
              canonicalPrimeSensitiveCert.p12
              canonicalPrimeSensitiveCert.p22
              canonicalPrimeSensitiveCert.theta_minus
              canonicalPrimeSensitiveCert.a01
              canonicalPrimeSensitiveCert.a02) ∧
            ratLe
              (thetaQuad canonicalPrimeSensitiveCert.a11
                canonicalPrimeSensitiveCert.a12
                canonicalPrimeSensitiveCert.a22
                canonicalPrimeSensitiveCert.p11
                canonicalPrimeSensitiveCert.p12
                canonicalPrimeSensitiveCert.p22
                canonicalPrimeSensitiveCert.theta_plus
                canonicalPrimeSensitiveCert.a01
                canonicalPrimeSensitiveCert.a02)
              (ratNeg canonicalPrimeSensitiveCert.epsilon) :=
  finite_weil_packet_prime_sensitive canonicalPrimeSensitiveCert

theorem canonical_margin_psd (c1 c2 : Rat) :
    ratLe ratZero
      (quad2 canonicalPrimeSensitiveCert.marginCert.b11
        canonicalPrimeSensitiveCert.marginCert.b12
        canonicalPrimeSensitiveCert.marginCert.b22 c1 c2) :=
  finite_weil_packet_margin_psd canonicalPrimeSensitiveCert c1 c2

end BEDC.Derived.RHRoute.WeilPrimeSensitivePacket

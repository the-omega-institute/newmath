import BEDC.Derived.ZModUp
import BEDC.Derived.CRTUp
import BEDC.Derived.GcdUp
import BEDC.Derived.PrimeUp.UnitResult
import BEDC.Algebra.Rel
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.CyclicGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.GcdUp
open BEDC.Derived.ZModUp
open BEDC.Derived.CRTUp
open BEDC.FKernel.ExternalBinary (bwordLength)

structure ZModAddGroupCore (n : BHist) where
  n_unary : UnaryHistory n
  n_nonempty : hsame n BHist.Empty -> False
  carrier : Type
  eqv : carrier -> carrier -> Prop
  eq_refl : ∀ x : carrier, eqv x x
  eq_symm : ∀ {x y : carrier}, eqv x y -> eqv y x
  eq_trans : ∀ {x y z : carrier}, eqv x y -> eqv y z -> eqv x z
  zero : carrier
  add : carrier -> carrier -> carrier
  neg : carrier -> carrier
  add_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (add x y) (add x' y')
  neg_respects : ∀ {x y : carrier}, eqv x y -> eqv (neg x) (neg y)
  add_comm : ∀ x y : carrier, eqv (add x y) (add y x)
  add_assoc : ∀ x y z : carrier, eqv (add (add x y) z) (add x (add y z))
  zero_add : ∀ x : carrier, eqv (add zero x) x
  add_zero : ∀ x : carrier, eqv (add x zero) x
  neg_add : ∀ x : carrier, eqv (add (neg x) x) zero
  add_neg : ∀ x : carrier, eqv (add x (neg x)) zero

def zmodAddGroupCore (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZModAddGroupCore n :=
  { n_unary := nUnary
    n_nonempty := nNonempty
    carrier := ZMod n
    eqv := zmodEq
    eq_refl := zmodEq_refl
    eq_symm := zmodEq_symm
    eq_trans := zmodEq_trans
    zero := zmodZero n nUnary nNonempty
    add := zmodAdd n nUnary nNonempty
    neg := zmodNeg n nUnary nNonempty
    add_respects := zmodAdd_congr nUnary nNonempty
    neg_respects := zmodNeg_congr nUnary nNonempty
    add_comm := zmodAdd_comm nUnary nNonempty
    add_assoc := zmodAdd_assoc nUnary nNonempty
    zero_add := zmodZero_add_left nUnary nNonempty
    add_zero := zmodZero_add_right nUnary nNonempty
    neg_add := zmodAdd_neg_left nUnary nNonempty
    add_neg := zmodAdd_neg_right nUnary nNonempty }

def zmodNatScale (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (k : BHist) (kUnary : UnaryHistory k) (a : ZMod n) : ZMod n :=
  zmodFromNat n nUnary nNonempty (natMulFn k a.val)
    (natMulFn_unary kUnary (zmodVal_unary nUnary a))

def ZModAnnihilates {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (k : BHist) (kUnary : UnaryHistory k) (a : ZMod n) : Prop :=
  zmodEq (zmodNatScale n nUnary nNonempty k kUnary a)
    (zmodZero n nUnary nNonempty)

def ZModOrder {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : BHist) : Prop :=
  ∃ kUnary : UnaryHistory k,
    (hsame k BHist.Empty -> False) ∧
      ZModAnnihilates nUnary nNonempty k kUnary a ∧
        ∀ j : BHist, ∀ jUnary : UnaryHistory j,
          (hsame j BHist.Empty -> False) ->
            NatUnaryStrictPrefix j k ->
              ZModAnnihilates nUnary nNonempty j jUnary a -> False

structure ZModOrderDivisorFragment {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) where
  exponent : BHist
  exponent_unary : UnaryHistory exponent
  exponent_nonempty : hsame exponent BHist.Empty -> False
  annihilates : ZModAnnihilates nUnary nNonempty exponent exponent_unary a
  divides_modulus : NatDivides exponent n

theorem zmodNatScale_modulus_zero {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) :
    ZModAnnihilates nUnary nNonempty n nUnary a := by
  unfold ZModAnnihilates zmodNatScale zmodFromNat zmodZero zmodEq
  change hsame (natModFn n (natMulFn n a.val)) BHist.Empty
  have aUnary : UnaryHistory a.val := zmodVal_unary nUnary a
  have productUnary : UnaryHistory (natMulFn n a.val) :=
    natMulFn_unary nUnary aUnary
  have dividesProduct : NatDivides n (natMulFn n a.val) :=
    ⟨a.val, aUnary, natMulFn_rel nUnary aUnary⟩
  exact (dvd_iff_mod_zero nUnary nNonempty productUnary).mp dividesProduct

theorem zmodNatScale_exponent_hsame_transport {n k k' : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (kUnary : UnaryHistory k)
    (k'Unary : UnaryHistory k')
    (a : ZMod n) :
    hsame k k' ->
      ZModAnnihilates nUnary nNonempty k kUnary a ->
        ZModAnnihilates nUnary nNonempty k' k'Unary a := by
  intro sameK annihilates
  unfold ZModAnnihilates zmodNatScale zmodEq at *
  change hsame (natModFn n (natMulFn k' a.val)) BHist.Empty
  have productSame :
      hsame (natMulFn k' a.val) (natMulFn k a.val) :=
    natMulFn_hsame_transport (hsame_symm sameK) (hsame_refl a.val)
  exact hsame_trans (natModFn_hsame_arg_transport (M := n) productSame) annihilates

def bhistIsEmpty : BHist -> Bool
  | BHist.Empty => true
  | BHist.e0 _ => false
  | BHist.e1 _ => false

theorem bhistIsEmpty_true {h : BHist} :
    bhistIsEmpty h = true -> hsame h BHist.Empty := by
  cases h with
  | Empty =>
      intro _hit
      rfl
  | e0 _ =>
      intro hit
      cases hit
  | e1 _ =>
      intro hit
      cases hit

def zmodAnnihilatesBool (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (k : BHist) (kUnary : UnaryHistory k) (a : ZMod n) : Bool :=
  bhistIsEmpty (zmodNatScale n nUnary nNonempty k kUnary a).val

theorem zmodAnnihilatesBool_true {n k : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (kUnary : UnaryHistory k)
    (a : ZMod n) :
    zmodAnnihilatesBool n nUnary nNonempty k kUnary a = true ->
      ZModAnnihilates nUnary nNonempty k kUnary a := by
  intro hit
  unfold zmodAnnihilatesBool at hit
  unfold ZModAnnihilates zmodEq zmodZero
  exact bhistIsEmpty_true hit

def zmodOrderSearchFrom (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Nat -> Nat -> Option BHist
  | _start, 0 => none
  | start, fuel + 1 =>
      if zmodAnnihilatesBool n nUnary nNonempty
          (natToUnary start) (natToUnary_unary start) a then
        some (natToUnary start)
      else
        zmodOrderSearchFrom n nUnary nNonempty a (start + 1) fuel

def zmodOrderSearch (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Option BHist :=
  zmodOrderSearchFrom n nUnary nNonempty a 1 (bwordLength n)

def zmodOrderValue (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : BHist :=
  match zmodOrderSearch n nUnary nNonempty a with
  | some k => k
  | none => n

def zmodModulusOrderDivisorFragment {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : ZModOrderDivisorFragment nUnary nNonempty a :=
  { exponent := n
    exponent_unary := nUnary
    exponent_nonempty := nNonempty
    annihilates := zmodNatScale_modulus_zero nUnary nNonempty a
    divides_modulus := (NatDivides_reflexive_pair nUnary).right }

def ZModGenerates {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (g : ZMod n) : Prop :=
  ∀ target : ZMod n, ∃ k : BHist, ∃ kUnary : UnaryHistory k,
    zmodEq (zmodNatScale n nUnary nNonempty k kUnary g) target

def ZModGeneratorGcdOne {n : BHist} (g : ZMod n) : Prop :=
  hsame (natGcdFn g.val n) NatOne

theorem NatGcd_one_left {n : BHist}
    (nUnary : UnaryHistory n) :
    NatGcd NatOne n NatOne := by
  have oneUnary : UnaryHistory NatOne := unary_e1_closed unary_empty
  constructor
  · exact oneUnary
  · constructor
    · exact nUnary
    · constructor
      · exact oneUnary
      · constructor
        · exact (NatDivides_reflexive_pair oneUnary).right
        · constructor
          · exact (NatDivides_reflexive_pair nUnary).left
          · intro d dividesOne _dividesN
            exact dividesOne

theorem natGcdFn_one_left_hsame {n : BHist}
    (nUnary : UnaryHistory n) :
    hsame (natGcdFn NatOne n) NatOne := by
  have oneUnary : UnaryHistory NatOne := unary_e1_closed unary_empty
  exact NatGcd_unique_hsame
    (natGcdFn_spec oneUnary nUnary)
    (NatGcd_one_left nUnary)

theorem natGcdFn_left_hsame_transport {a a' n : BHist} :
    hsame a a' -> hsame (natGcdFn a n) (natGcdFn a' n) := by
  intro same
  cases same
  rfl

private theorem zmod_common_divisor_mod_remainder {n x r d : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (xUnary : UnaryHistory x)
    (sameR : hsame (natModFn n x) r)
    (dividesX : NatDivides d x)
    (dividesN : NatDivides d n) :
    NatDivides d r := by
  have divrem : NatDivRem n x (natQuotFn n x) (natModFn n x) :=
    natModFn_spec nUnary xUnary nNonempty
  cases divrem with
  | intro nq data =>
      have dUnary : UnaryHistory d := NatDivides_divisor_unary dividesN
      have dNonempty : hsame d BHist.Empty -> False := by
        intro dEmpty
        cases dEmpty
        exact nNonempty (NatDivides_empty_left_result_empty dividesN)
      have nDividesProduct : NatDivides n nq :=
        ⟨natQuotFn n x, NatMul_right_unary data.left, data.left⟩
      have dDividesProduct : NatDivides d nq :=
        NatDivides_transitive dividesN nDividesProduct
      have dividesRemainder : NatDivides d (natModFn n x) :=
        dvd_tail_of_dvd_sum dUnary dNonempty data.right.left dDividesProduct dividesX
      exact (NatDivides_dividend_hsame_transport dividesRemainder sameR).right

theorem zmod_generator_gcd_one_of_generates {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (g : ZMod n)
    (generates : ZModGenerates nUnary nNonempty g) :
    ZModGeneratorGcdOne g := by
  cases generates (zmodOne n nUnary nNonempty) with
  | intro k kData =>
      cases kData with
      | intro kUnary generatedOne =>
          unfold ZModGeneratorGcdOne
          have gUnary : UnaryHistory g.val := zmodVal_unary nUnary g
          have gcdSpec : NatGcd g.val n (natGcdFn g.val n) :=
            natGcdFn_spec gUnary nUnary
          have gcdUnary : UnaryHistory (natGcdFn g.val n) :=
            NatGcd_result_unary gcdSpec
          have gcdDividesG : NatDivides (natGcdFn g.val n) g.val :=
            NatGcd_dvd_left gcdSpec
          have gcdDividesN : NatDivides (natGcdFn g.val n) n :=
            NatGcd_dvd_right gcdSpec
          have productUnary : UnaryHistory (natMulFn k g.val) :=
            natMulFn_unary kUnary gUnary
          have gcdDividesProduct : NatDivides (natGcdFn g.val n) (natMulFn k g.val) := by
            have productMul : NatMul g.val k (natMulFn k g.val) := by
              have computed : NatMul k g.val (natMulFn k g.val) :=
                natMulFn_rel kUnary gUnary
              have direct : NatMul g.val k (natMulFn g.val k) :=
                natMulFn_rel gUnary kUnary
              have sameProduct : hsame (natMulFn g.val k) (natMulFn k g.val) :=
                NatMul_comm_hsame gUnary kUnary direct computed
              exact (NatMul_result_hsame_transport direct sameProduct).right
            exact NatDivides_transitive gcdDividesG
              ⟨k, kUnary, productMul⟩
          have remOne :
              hsame (natModFn n (natMulFn k g.val)) (natModFn n NatOne) := by
            change hsame (natModFn n (natMulFn k g.val)) (natModFn n NatOne) at generatedOne
            exact generatedOne
          have gcdDividesModOne :
              NatDivides (natGcdFn g.val n) (natModFn n NatOne) :=
            zmod_common_divisor_mod_remainder nUnary nNonempty productUnary remOne
              gcdDividesProduct gcdDividesN
          have divremOne : NatDivRem n NatOne (natQuotFn n NatOne) (natModFn n NatOne) :=
            natModFn_spec nUnary (unary_e1_closed unary_empty) nNonempty
          have dividesOne : NatDivides (natGcdFn g.val n) NatOne := by
            cases divremOne with
            | intro nq data =>
                have gcdDividesNQ : NatDivides (natGcdFn g.val n) nq :=
                  NatDivides_mul_right_factor_closed
                    (NatMul_right_unary data.left) gcdDividesN data.left
                exact NatDivides_cont_closed gcdDividesNQ gcdDividesModOne
                  data.right.left.right.right
          exact NatDivides_unit_right_iff.mp dividesOne

theorem zmodGenerator_of_gcd_one_nonempty {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (g : ZMod n)
    (gNonempty : hsame g.val BHist.Empty -> False)
    (coprime : ZModGeneratorGcdOne g) :
    ZModGenerates nUnary nNonempty g := by
  intro target
  let gUnary : UnaryHistory g.val := zmodVal_unary nUnary g
  let zeroG : ZMod g.val := zmodZero g.val gUnary gNonempty
  let pair : ZMod g.val × ZMod n := (zeroG, target)
  let x : ZMod (crtModulus g.val n) :=
    crtInverse gUnary nUnary gNonempty nNonempty pair
  have xUnary : UnaryHistory x.val :=
    zmodVal_unary (crtModulus_unary gUnary nUnary) x
  have leftZero :
      zmodEq (crtForward gUnary nUnary gNonempty nNonempty x).1 zeroG :=
    crt_right_inv_left gUnary nUnary gNonempty nNonempty coprime pair
  have leftModZero :
      hsame (natModFn g.val x.val) BHist.Empty := by
    change hsame (natModFn g.val x.val) BHist.Empty at leftZero
    exact leftZero
  have rightTarget :
      zmodEq (crtForward gUnary nUnary gNonempty nNonempty x).2 target :=
    crt_right_inv_right gUnary nUnary gNonempty nNonempty coprime pair
  have rightModTarget :
      hsame (natModFn n x.val) target.val := by
    change hsame (natModFn n x.val) target.val at rightTarget
    exact rightTarget
  have dividesByG : NatDivides g.val x.val :=
    (dvd_iff_mod_zero gUnary gNonempty xUnary).mpr leftModZero
  cases dividesByG with
  | intro k kData =>
      have kUnary : UnaryHistory k := kData.left
      have productSame : hsame (natMulFn k g.val) x.val := by
        have computed : NatMul k g.val (natMulFn k g.val) :=
          natMulFn_rel kUnary gUnary
        have sameForward : hsame x.val (natMulFn k g.val) :=
          NatMul_comm_hsame gUnary kUnary kData.right computed
        exact hsame_symm sameForward
      have scaledToX :
          hsame (natModFn n (natMulFn k g.val)) (natModFn n x.val) :=
        natModFn_hsame_arg_transport (M := n) productSame
      refine ⟨k, kUnary, ?_⟩
      change hsame (natModFn n (natMulFn k g.val)) target.val
      exact hsame_trans scaledToX rightModTarget

theorem zmodOne_gcd_one_of_unit_strict {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (unitStrict : NatUnaryStrictPrefix NatOne n) :
    ZModGeneratorGcdOne (zmodOne n nUnary nNonempty) := by
  unfold ZModGeneratorGcdOne zmodOne
  have oneUnary : UnaryHistory NatOne := unary_e1_closed unary_empty
  have oneMod : hsame (natModFn n NatOne) NatOne :=
    natModFn_of_strict nUnary nNonempty oneUnary unitStrict
  exact hsame_trans
    (natGcdFn_left_hsame_transport oneMod)
    (natGcdFn_one_left_hsame nUnary)

theorem zmodNatScale_one {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (target : ZMod n) :
    zmodEq
      (zmodNatScale n nUnary nNonempty target.val
        (zmodVal_unary nUnary target) (zmodOne n nUnary nNonempty))
      target := by
  unfold zmodNatScale zmodFromNat zmodOne zmodEq
  change hsame
    (natModFn n (natMulFn target.val (natModFn n NatOne))) target.val
  have targetUnary : UnaryHistory target.val := zmodVal_unary nUnary target
  have oneUnary : UnaryHistory NatOne := unary_e1_closed unary_empty
  have reduceOne :
      hsame (natModFn n (natMulFn target.val (natModFn n NatOne)))
        (natModFn n (natMulFn target.val NatOne)) :=
    natModFn_mul_right_reduce_same_mod nUnary nNonempty targetUnary oneUnary
  have unitRight :
      hsame (natModFn n (natMulFn target.val NatOne))
        (natModFn n target.val) :=
    natModFn_hsame_arg_transport (M := n)
      (natMulFn_unit_right_same targetUnary)
  exact hsame_trans reduceOne
    (hsame_trans unitRight
      (natModFn_of_strict nUnary nNonempty targetUnary target.isLt))

theorem zmodOne_generates {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) :
    ZModGenerates nUnary nNonempty (zmodOne n nUnary nNonempty) := by
  intro target
  exact ⟨target.val, zmodVal_unary nUnary target,
    zmodNatScale_one nUnary nNonempty target⟩

theorem zmod_cyclic_exists {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) :
    ∃ g : ZMod n, ZModGenerates nUnary nNonempty g := by
  exact ⟨zmodOne n nUnary nNonempty, zmodOne_generates nUnary nNonempty⟩

theorem zmod_strict_unit_cyclic_gcd_exists {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (unitStrict : NatUnaryStrictPrefix NatOne n) :
    ∃ g : ZMod n, ZModGenerates nUnary nNonempty g ∧ ZModGeneratorGcdOne g := by
  exact ⟨zmodOne n nUnary nNonempty,
    zmodOne_generates nUnary nNonempty,
    zmodOne_gcd_one_of_unit_strict nUnary nNonempty unitStrict⟩

end BEDC.Derived.CyclicGroupUp

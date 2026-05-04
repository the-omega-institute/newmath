import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def PadicPrimeScale (p exponent result : BHist) : Prop :=
  NatPrime p ∧ NatMul p exponent result

theorem PadicPrimeScale_total {p exponent : BHist} :
    NatPrime p -> UnaryHistory exponent ->
      ∃ result : BHist, UnaryHistory result ∧ PadicPrimeScale p exponent result := by
  intro prime exponentUnary
  have product := NatMul_total prime.left exponentUnary
  cases product with
  | intro result data =>
      exact ⟨result, data.left, And.intro prime data.right⟩

theorem PadicPrimeScale_exists_unique {p exponent : BHist} :
    NatPrime p -> UnaryHistory exponent ->
      exists result : BHist, PadicPrimeScale p exponent result ∧
        forall other : BHist, PadicPrimeScale p exponent other -> hsame result other := by
  intro prime exponentUnary
  have total := PadicPrimeScale_total prime exponentUnary
  cases total with
  | intro result data =>
      exact Exists.intro result
        (And.intro data.right
          (fun other otherScale => NatMul_functional prime.left data.right.right otherScale.right))

theorem PadicPrimeScale_empty_result_iff_empty_exponent {p exponent result : BHist} :
    PadicPrimeScale p exponent result ->
      (hsame result BHist.Empty ↔ hsame exponent BHist.Empty) := by
  intro scale
  constructor
  · intro resultEmpty
    have primeNonempty : hsame p BHist.Empty -> False := by
      intro primeEmpty
      cases primeEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd scale.left.right.left
    cases resultEmpty
    exact Iff.mp
      (NatMul_nonempty_multiplicand_empty_result_iff scale.left.left primeNonempty)
      scale.right
  · intro exponentEmpty
    cases exponentEmpty
    cases scale.right with
    | zero _unary =>
        rfl

theorem PadicPrimeScale_succ_exponent_inversion {p q r : BHist} :
    PadicPrimeScale p (BHist.e1 q) r ->
      ∃ n : BHist, PadicPrimeScale p q n ∧ Cont n p r := by
  intro scale
  have inversion := NatMul_succ_inversion scale.right
  cases inversion with
  | intro n data =>
      exact ⟨n, ⟨scale.left, data.left⟩, data.right⟩

theorem PadicPrimeScale_append_cont_closure {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p (append w q) r := by
  intro left right continuation
  exact And.intro left.left (NatMul_append_cont left.right right.right continuation)

theorem PadicPrimeScale_append_cont_result_functional {p w q n e r r' : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p (append w q) r' -> hsame r r' := by
  intro left right continuation other
  have combined : PadicPrimeScale p (append w q) r :=
    PadicPrimeScale_append_cont_closure left right continuation
  exact NatMul_functional left.left.left combined.right other.right

theorem PadicPrimeScale_append_total {p w q : BHist} :
    NatPrime p -> UnaryHistory w -> UnaryHistory q ->
      Exists (fun r : BHist => PadicPrimeScale p (append w q) r ∧
        Exists (fun n : BHist => Exists (fun e : BHist =>
          PadicPrimeScale p w n ∧ PadicPrimeScale p q e ∧ Cont n e r))) := by
  intro primeP unaryW unaryQ
  have leftTotal := NatMul_total primeP.left unaryW
  have rightTotal := NatMul_total primeP.left unaryQ
  cases leftTotal with
  | intro n leftData =>
      cases rightTotal with
      | intro e rightData =>
          have leftScale : PadicPrimeScale p w n :=
            And.intro primeP leftData.right
          have rightScale : PadicPrimeScale p q e :=
            And.intro primeP rightData.right
          have continuation : Cont n e (append n e) :=
            cont_intro rfl
          exact Exists.intro (append n e)
            (And.intro
              (PadicPrimeScale_append_cont_closure leftScale rightScale continuation)
              (Exists.intro n
                (Exists.intro e (And.intro leftScale (And.intro rightScale continuation)))))

theorem PadicPrimeScale_append_empty_result_empty_factors_iff {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      (hsame r BHist.Empty <-> hsame w BHist.Empty ∧ hsame q BHist.Empty) := by
  intro left right continuation
  have combined : PadicPrimeScale p (append w q) r :=
    PadicPrimeScale_append_cont_closure left right continuation
  have resultIff := PadicPrimeScale_empty_result_iff_empty_exponent combined
  constructor
  · intro resultEmpty
    exact append_eq_empty_iff.mp (Iff.mp resultIff resultEmpty)
  · intro partsEmpty
    exact Iff.mpr resultIff (append_eq_empty_iff.mpr partsEmpty)

theorem PadicPrimeScale_append_visible_exponent_result_nonempty {p q n e r tail : BHist} :
    (PadicPrimeScale p (BHist.e0 tail) n -> PadicPrimeScale p q e -> Cont n e r ->
      hsame r BHist.Empty -> False) ∧
    (PadicPrimeScale p (BHist.e1 tail) n -> PadicPrimeScale p q e -> Cont n e r ->
      hsame r BHist.Empty -> False) := by
  constructor
  · intro left right continuation resultEmpty
    have emptyParts :=
      Iff.mp
        (PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation)
        resultEmpty
    exact not_hsame_e0_empty emptyParts.left
  · intro left right continuation resultEmpty
    have emptyParts :=
      Iff.mp
        (PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation)
        resultEmpty
    exact not_hsame_e1_empty emptyParts.left

theorem PadicPrimeScale_append_visible_right_exponent_result_nonempty {p w n e r tail : BHist} :
    (PadicPrimeScale p w n -> PadicPrimeScale p (BHist.e0 tail) e -> Cont n e r ->
      hsame r BHist.Empty -> False) ∧
    (PadicPrimeScale p w n -> PadicPrimeScale p (BHist.e1 tail) e -> Cont n e r ->
      hsame r BHist.Empty -> False) := by
  constructor
  · intro left right continuation resultEmpty
    have emptyParts :=
      Iff.mp
        (PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation)
        resultEmpty
    exact not_hsame_e0_empty emptyParts.right
  · intro left right continuation resultEmpty
    have emptyParts :=
      Iff.mp
        (PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation)
        resultEmpty
    exact not_hsame_e1_empty emptyParts.right

theorem PadicPrimeScale_visible_exponent_result_nonempty {p result tail : BHist} :
    (PadicPrimeScale p (BHist.e0 tail) result -> hsame result BHist.Empty -> False) ∧
      (PadicPrimeScale p (BHist.e1 tail) result -> hsame result BHist.Empty -> False) := by
  constructor
  · intro scale resultEmpty
    exact not_hsame_e0_empty
      (Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty)
  · intro scale resultEmpty
    exact not_hsame_e1_empty
      (Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty)

theorem PadicPrimeScale_empty_exponent_result_empty {p exponent : BHist} :
    NatPrime p -> hsame exponent BHist.Empty -> PadicPrimeScale p exponent BHist.Empty := by
  intro prime exponentEmpty
  cases exponentEmpty
  exact And.intro prime (NatMul.zero prime.left)

theorem PadicPrimeScale_first_prime_unit_exponent_result :
    PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty)
      (BHist.e1 (BHist.e1 BHist.Empty)) := by
  exact And.intro NatPrime_first_pair.left NatMul_first_prime_unit_result

end BEDC.Derived.PadicUp

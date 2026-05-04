import BEDC.Derived.PrimeUp.NatMulCases
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def PadicPrimeScale (p exponent result : BHist) : Prop :=
  NatPrime p ∧ NatMul p exponent result

theorem PadicPrimeScale_unary_components {p exponent result : BHist} :
    PadicPrimeScale p exponent result ->
      UnaryHistory p /\ UnaryHistory exponent /\ UnaryHistory result := by
  intro scale
  exact And.intro scale.left.left
    (And.intro (NatMul_right_unary scale.right)
      (NatMul_result_unary scale.left.left scale.right))

theorem PadicPrimeScale_total {p exponent : BHist} :
    NatPrime p -> UnaryHistory exponent ->
      ∃ result : BHist, UnaryHistory result ∧ PadicPrimeScale p exponent result := by
  intro prime exponentUnary
  have product := NatMul_total prime.left exponentUnary
  cases product with
  | intro result data =>
      exact ⟨result, data.left, And.intro prime data.right⟩

theorem PadicPrimeScale_result_semanticNameCert {p exponent : BHist} :
    NatPrime p -> UnaryHistory exponent ->
      SemanticNameCert (fun result : BHist => PadicPrimeScale p exponent result)
        (fun result : BHist => PadicPrimeScale p exponent result)
        (fun result : BHist => PadicPrimeScale p exponent result) hsame := by
  intro prime exponentUnary
  have total := PadicPrimeScale_total prime exponentUnary
  exact {
    core := {
      carrier_inhabited := by
        cases total with
        | intro result data =>
            exact Exists.intro result data.right
      equiv_refl := by
        intro result _scale
        exact hsame_refl result
      equiv_symm := by
        intro result other same
        exact hsame_symm same
      equiv_trans := by
        intro result other final sameRO sameOF
        exact hsame_trans sameRO sameOF
      carrier_respects_equiv := by
        intro result other same scale
        cases same
        exact scale
    }
    pattern_sound := by
      intro result source
      exact source
    ledger_sound := by
      intro result source
      exact source
  }

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

theorem PadicPrimeScale_positive_exponent_cont_readback {p exponent result : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      PadicPrimeScale p exponent result ->
        ∃ tail : BHist, ∃ pred : BHist,
          UnaryHistory tail ∧ exponent = BHist.e1 tail ∧
            PadicPrimeScale p tail pred ∧ Cont pred p result := by
  intro exponentUnary exponentNonempty scale
  have exponentTail := unary_history_nonempty_e1_tail exponentUnary exponentNonempty
  cases exponentTail with
  | intro tail data =>
      cases data.left
      have inversion := PadicPrimeScale_succ_exponent_inversion scale
      cases inversion with
      | intro pred predData =>
          exact ⟨tail, pred, data.right, rfl, predData.left, predData.right⟩

theorem PadicPrimeScale_succ_exponent_factorization_iff {p q r : BHist} :
    PadicPrimeScale p (BHist.e1 q) r ↔
      ∃ n : BHist, PadicPrimeScale p q n ∧ Cont n p r := by
  constructor
  · intro scale
    exact PadicPrimeScale_succ_exponent_inversion scale
  · intro factors
    cases factors with
    | intro n data =>
        exact And.intro data.left.left (NatMul.succ data.left.right data.right)

theorem PadicPrimeScale_exponent_result_cases {p exponent result : BHist} :
    PadicPrimeScale p exponent result ->
      (hsame exponent BHist.Empty ∧ hsame result BHist.Empty) ∨
        ∃ tail pred : BHist,
          exponent = BHist.e1 tail ∧ PadicPrimeScale p tail pred ∧ Cont pred p result := by
  intro scale
  have mulCases := NatMul_exponent_result_cases scale.right
  cases mulCases with
  | inl emptyCase =>
      exact Or.inl emptyCase
  | inr succCase =>
      cases succCase with
      | intro tail tailData =>
          cases tailData with
          | intro pred data =>
              exact Or.inr ⟨tail, pred, data.left, ⟨scale.left, data.right.left⟩,
                data.right.right⟩

theorem PadicPrimeScale_succ_exponent_predecessor_unique {p q r : BHist} :
    PadicPrimeScale p (BHist.e1 q) r ->
      ∃ n : BHist, PadicPrimeScale p q n ∧ Cont n p r ∧
        ∀ m : BHist, PadicPrimeScale p q m -> hsame n m := by
  intro scale
  have inversion := PadicPrimeScale_succ_exponent_inversion scale
  cases inversion with
  | intro n data =>
      exact Exists.intro n
          (And.intro data.left
            (And.intro data.right
              (fun m otherScale =>
                NatMul_functional scale.left.left data.left.right otherScale.right)))

theorem PadicPrimeScale_unit_exponent_result_prime_hsame {p result : BHist} :
    PadicPrimeScale p (BHist.e1 BHist.Empty) result -> hsame result p := by
  intro scale
  have inversion := PadicPrimeScale_succ_exponent_inversion scale
  cases inversion with
  | intro n data =>
      have nEmpty : hsame n BHist.Empty :=
        Iff.mpr (PadicPrimeScale_empty_result_iff_empty_exponent data.left)
          (hsame_refl BHist.Empty)
      exact cont_respects_hsame nEmpty (hsame_refl p) data.right (cont_left_unit p)

theorem PadicPrimeScale_append_cont_closure {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p (append w q) r := by
  intro left right continuation
  exact And.intro left.left (NatMul_append_cont left.right right.right continuation)

theorem PadicNatMul_append_exponent_decomposition {d w q r : BHist} :
    UnaryHistory d -> UnaryHistory w -> UnaryHistory q -> NatMul d (append w q) r ->
      ∃ n : BHist, ∃ e : BHist, NatMul d w n ∧ NatMul d q e ∧ Cont n e r := by
  intro unaryD unaryW unaryQ mul
  induction q generalizing r with
  | Empty =>
      exact
        Exists.intro r
          (Exists.intro BHist.Empty
            (And.intro mul (And.intro (NatMul.zero unaryD) (cont_right_unit r))))
  | e0 tail _ih =>
      cases unaryQ
  | e1 tail ih =>
      have tailUnary : UnaryHistory tail := unaryQ
      have split := NatMul_succ_inversion mul
      cases split with
      | intro part partData =>
          have decomposed := ih tailUnary partData.left
          cases decomposed with
          | intro n leftData =>
              cases leftData with
              | intro e rightData =>
                  have rightStep : NatMul d (BHist.e1 tail) (append e d) :=
                    NatMul.succ rightData.right.left (cont_intro rfl)
                  have joined : Cont n (append e d) r := by
                    cases rightData.right.right
                    cases partData.right
                    exact cont_intro (append_assoc n e d)
                  exact
                    Exists.intro n
                      (Exists.intro (append e d)
                        (And.intro rightData.left (And.intro rightStep joined)))

theorem PadicPrimeScale_append_factorization_iff {p w q r : BHist}
    (unaryW : UnaryHistory w) (unaryQ : UnaryHistory q) :
    PadicPrimeScale p (append w q) r <->
      Exists (fun n : BHist => Exists (fun e : BHist =>
        PadicPrimeScale p w n ∧ PadicPrimeScale p q e ∧ Cont n e r)) := by
  constructor
  · intro scale
    have decomposed :=
      PadicNatMul_append_exponent_decomposition scale.left.left unaryW unaryQ scale.right
    cases decomposed with
    | intro n leftData =>
        cases leftData with
        | intro e rightData =>
            exact Exists.intro n
              (Exists.intro e
                (And.intro (And.intro scale.left rightData.left)
                  (And.intro (And.intro scale.left rightData.right.left)
                    rightData.right.right)))
  · intro factors
    cases factors with
    | intro n leftData =>
        cases leftData with
        | intro e rightData =>
            exact PadicPrimeScale_append_cont_closure rightData.left rightData.right.left
              rightData.right.right

theorem PadicPrimeScale_append_exponent_decomposition {p w q r : BHist} :
    UnaryHistory w -> UnaryHistory q -> PadicPrimeScale p (append w q) r ->
      ∃ n : BHist, ∃ e : BHist,
        PadicPrimeScale p w n ∧ PadicPrimeScale p q e ∧ Cont n e r := by
  intro unaryW unaryQ scale
  have decomposed :=
    PadicNatMul_append_exponent_decomposition scale.left.left unaryW unaryQ scale.right
  cases decomposed with
  | intro n nData =>
      cases nData with
      | intro e eData =>
          exact
            Exists.intro n
              (Exists.intro e
                (And.intro (And.intro scale.left eData.left)
                  (And.intro (And.intro scale.left eData.right.left) eData.right.right)))

theorem PadicPrimeScale_append_succ_right_exponent_factorization_iff {p w q r : BHist} :
    UnaryHistory w -> UnaryHistory q ->
      (PadicPrimeScale p (append w (BHist.e1 q)) r <->
        ∃ n : BHist, ∃ e : BHist, ∃ step : BHist,
          PadicPrimeScale p w n ∧ PadicPrimeScale p q e ∧ Cont e p step ∧
            Cont n step r) := by
  intro unaryW unaryQ
  constructor
  · intro scale
    have decomposed :=
      PadicPrimeScale_append_exponent_decomposition unaryW (unary_e1_closed unaryQ) scale
    cases decomposed with
    | intro n nData =>
        cases nData with
        | intro step stepData =>
            have rightInversion := PadicPrimeScale_succ_exponent_inversion stepData.right.left
            cases rightInversion with
            | intro e eData =>
                exact Exists.intro n
                  (Exists.intro e
                    (Exists.intro step
                      (And.intro stepData.left
                        (And.intro eData.left (And.intro eData.right stepData.right.right)))))
  · intro factors
    cases factors with
    | intro n nData =>
        cases nData with
        | intro e eData =>
            cases eData with
            | intro step stepData =>
                have rightScale : PadicPrimeScale p (BHist.e1 q) step :=
                  Iff.mpr PadicPrimeScale_succ_exponent_factorization_iff
                    (Exists.intro e (And.intro stepData.right.left stepData.right.right.left))
                exact PadicPrimeScale_append_cont_closure stepData.left rightScale
                  stepData.right.right.right

theorem PadicPrimeScale_append_succ_left_exponent_factorization_iff {p w q r : BHist} :
    UnaryHistory w -> UnaryHistory q ->
      (PadicPrimeScale p (append (BHist.e1 w) q) r <->
        ∃ n : BHist, ∃ e : BHist, ∃ step : BHist,
          PadicPrimeScale p w n ∧ Cont n p step ∧ PadicPrimeScale p q e ∧
            Cont step e r) := by
  intro unaryW unaryQ
  constructor
  · intro scale
    have decomposed :=
      PadicPrimeScale_append_exponent_decomposition (unary_e1_closed unaryW) unaryQ scale
    cases decomposed with
    | intro step stepData =>
        cases stepData with
        | intro e eData =>
            have leftInversion := PadicPrimeScale_succ_exponent_inversion eData.left
            cases leftInversion with
            | intro n nData =>
                exact Exists.intro n
                  (Exists.intro e
                    (Exists.intro step
                      (And.intro nData.left
                        (And.intro nData.right
                          (And.intro eData.right.left eData.right.right)))))
  · intro factors
    cases factors with
    | intro n nData =>
        cases nData with
        | intro e eData =>
            cases eData with
            | intro step stepData =>
                have leftScale : PadicPrimeScale p (BHist.e1 w) step :=
                  Iff.mpr PadicPrimeScale_succ_exponent_factorization_iff
                    (Exists.intro n (And.intro stepData.left stepData.right.left))
                exact PadicPrimeScale_append_cont_closure leftScale stepData.right.right.left
                  stepData.right.right.right

theorem PadicPrimeScale_append_unit_right_factorization_iff {p w r : BHist} :
    UnaryHistory w ->
      (PadicPrimeScale p (append w (BHist.e1 BHist.Empty)) r <->
        ∃ n : BHist, PadicPrimeScale p w n ∧ Cont n p r) := by
  intro unaryW
  constructor
  · intro scale
    have decomposed :=
      PadicPrimeScale_append_exponent_decomposition unaryW (unary_e1_closed unary_empty) scale
    cases decomposed with
    | intro n nData =>
        cases nData with
        | intro e eData =>
            have sameE : hsame e p :=
              PadicPrimeScale_unit_exponent_result_prime_hsame eData.right.left
            cases sameE
            exact Exists.intro n (And.intro eData.left eData.right.right)
  · intro factors
    cases factors with
    | intro n data =>
        have emptyScale : PadicPrimeScale p BHist.Empty BHist.Empty :=
          And.intro data.left.left (NatMul.zero data.left.left.left)
        have unitScale : PadicPrimeScale p (BHist.e1 BHist.Empty) p :=
          Iff.mpr PadicPrimeScale_succ_exponent_factorization_iff
            (Exists.intro BHist.Empty (And.intro emptyScale (cont_left_unit p)))
        exact PadicPrimeScale_append_cont_closure data.left unitScale data.right

theorem PadicPrimeScale_append_cont_result_functional {p w q n e r r' : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p (append w q) r' -> hsame r r' := by
  intro left right continuation other
  have combined : PadicPrimeScale p (append w q) r :=
    PadicPrimeScale_append_cont_closure left right continuation
  exact NatMul_functional left.left.left combined.right other.right

theorem PadicPrimeScale_append_factor_results_unique {p w q n e r n2 e2 r2 : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p w n2 -> PadicPrimeScale p q e2 -> Cont n2 e2 r2 ->
        hsame n n2 ∧ hsame e e2 ∧ hsame r r2 := by
  intro left right continuation left2 right2 continuation2
  have sameN : hsame n n2 :=
    NatMul_functional left.left.left left.right left2.right
  have sameE : hsame e e2 :=
    NatMul_functional right.left.left right.right right2.right
  have sameR : hsame r r2 :=
    cont_respects_hsame sameN sameE continuation continuation2
  exact And.intro sameN (And.intro sameE sameR)

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

theorem PadicPrimeScale_append_empty_factor_result_hsame {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      (hsame w BHist.Empty -> hsame r e) ∧ (hsame q BHist.Empty -> hsame r n) := by
  intro left right continuation
  constructor
  · intro wEmpty
    have nEmpty : hsame n BHist.Empty :=
      Iff.mpr (PadicPrimeScale_empty_result_iff_empty_exponent left) wEmpty
    exact cont_respects_hsame nEmpty (hsame_refl e) continuation (cont_left_unit e)
  · intro qEmpty
    have eEmpty : hsame e BHist.Empty :=
      Iff.mpr (PadicPrimeScale_empty_result_iff_empty_exponent right) qEmpty
    exact cont_respects_hsame (hsame_refl n) eEmpty continuation (cont_right_unit n)

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

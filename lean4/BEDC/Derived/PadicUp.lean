import BEDC.Derived.IntUp
import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def PadicPrimeScale (p exponent result : BHist) : Prop :=
  NatPrime p ∧ NatMul p exponent result

theorem PadicPrimeScale_unary_components {p exponent result : BHist} :
    PadicPrimeScale p exponent result ->
      UnaryHistory p /\ UnaryHistory exponent /\ UnaryHistory result := by
  intro scale
  exact And.intro scale.left.left
    (And.intro (NatMul_right_unary scale.right)
      (NatMul_result_unary scale.left.left scale.right))

theorem PadicPrimeScale_prime_exponent_comm_hsame {p q r s : BHist} :
    UnaryHistory p -> UnaryHistory q -> PadicPrimeScale p q r -> PadicPrimeScale q p s ->
      hsame r s := by
  intro hp hq left right
  exact NatMul_comm_hsame hp hq left.right right.right

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

theorem PadicPrimeScale_unit_exponent_prime {p : BHist} :
    NatPrime p -> PadicPrimeScale p (BHist.e1 BHist.Empty) p := by
  intro prime
  exact And.intro prime (NatMul.succ (NatMul.zero prime.left) (cont_left_unit p))

theorem PadicPrimeScale_unit_exponent_result_prime {p : BHist} :
    NatPrime p -> PadicPrimeScale p (BHist.e1 BHist.Empty) p := by
  intro prime
  exact And.intro prime
    (NatMul.succ (NatMul.zero prime.left) (cont_left_unit p))

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

theorem PadicPrimeScale_append_unit_right_predecessor_unique {p w r : BHist} :
    UnaryHistory w -> PadicPrimeScale p (append w (BHist.e1 BHist.Empty)) r ->
      exists n : BHist, PadicPrimeScale p w n ∧ Cont n p r ∧
        forall other : BHist, PadicPrimeScale p w other -> hsame n other := by
  intro unaryW scale
  have factors :=
    Iff.mp (PadicPrimeScale_append_unit_right_factorization_iff unaryW) scale
  cases factors with
  | intro n data =>
      exact Exists.intro n
        (And.intro data.left
          (And.intro data.right
            (fun other otherScale =>
              NatMul_functional scale.left.left data.left.right otherScale.right)))

theorem PadicPrimeScale_append_unit_right_result_hsame {p w n r : BHist} :
    UnaryHistory w -> PadicPrimeScale p w n ->
      PadicPrimeScale p (append w (BHist.e1 BHist.Empty)) r ->
        hsame r (append n p) := by
  intro unaryW leftScale rightScale
  have predecessor :=
    PadicPrimeScale_append_unit_right_predecessor_unique unaryW rightScale
  cases predecessor with
  | intro pred data =>
      have samePredN : hsame pred n := data.right.right n leftScale
      exact cont_respects_hsame samePredN (hsame_refl p) data.right.left (cont_intro rfl)

theorem PadicPrimeScale_append_unit_left_factorization_iff {p q r : BHist} :
    UnaryHistory q ->
      (PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) r <->
        ∃ e : BHist, PadicPrimeScale p q e ∧ Cont p e r) := by
  intro unaryQ
  constructor
  · intro scale
    have decomposed :=
      PadicPrimeScale_append_exponent_decomposition (unary_e1_closed unary_empty) unaryQ scale
    cases decomposed with
    | intro n nData =>
        cases nData with
        | intro e eData =>
            have sameN : hsame n p :=
              PadicPrimeScale_unit_exponent_result_prime_hsame eData.left
            cases sameN
            exact Exists.intro e (And.intro eData.right.left eData.right.right)
  · intro factors
    cases factors with
    | intro e data =>
        have emptyScale : PadicPrimeScale p BHist.Empty BHist.Empty :=
          And.intro data.left.left (NatMul.zero data.left.left.left)
        have unitScale : PadicPrimeScale p (BHist.e1 BHist.Empty) p :=
          Iff.mpr PadicPrimeScale_succ_exponent_factorization_iff
            (Exists.intro BHist.Empty (And.intro emptyScale (cont_left_unit p)))
        exact PadicPrimeScale_append_cont_closure unitScale data.left data.right

theorem PadicPrimeScale_append_unit_left_predecessor_unique {p q r : BHist} :
    UnaryHistory q -> PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) r ->
      Exists (fun e : BHist => PadicPrimeScale p q e ∧ Cont p e r ∧
        forall other : BHist, PadicPrimeScale p q other -> hsame e other) := by
  intro unaryQ scale
  have factors :=
    Iff.mp (PadicPrimeScale_append_unit_left_factorization_iff (p := p) (q := q)
      (r := r) unaryQ) scale
  cases factors with
  | intro e data =>
      exact Exists.intro e
        (And.intro data.left
          (And.intro data.right
            (fun other otherScale =>
              NatMul_functional scale.left.left data.left.right otherScale.right)))

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

theorem PadicPrimeScale_append_unit_exponents_result_square_hsame {p result : BHist} :
    PadicPrimeScale p (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) result ->
      hsame result (append p p) := by
  intro scale
  have unitScale : PadicPrimeScale p (BHist.e1 BHist.Empty) p :=
    PadicPrimeScale_unit_exponent_prime scale.left
  have squareScale :
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
        (append p p) :=
    PadicPrimeScale_append_cont_closure unitScale unitScale (cont_intro rfl)
  exact NatMul_functional scale.left.left scale.right squareScale.right
theorem PadicPrimeScale_append_unit_exponents_result_not_empty {p result : BHist} :
    PadicPrimeScale p (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) result ->
      hsame result BHist.Empty -> False := by
  intro scale resultEmpty
  have pEmpty := (append_eq_empty_iff.mp (hsame_trans (hsame_symm
    (PadicPrimeScale_append_unit_exponents_result_square_hsame scale)) resultEmpty)).left
  cases scale.left.right.left with
  | intro tail data => exact data.right.left (cont_empty_result_inversion
      (cont_result_hsame_transport data.right.right pEmpty)).right

abbrev NatOne : BHist := BHist.e1 BHist.Empty

inductive PPow (p : BHist) : BHist -> BHist -> Prop where
  | zero (hp : UnaryHistory p) : PPow p BHist.Empty NatOne
  | succ {n r r' : BHist} : PPow p n r -> NatMul p r r' -> PPow p (BHist.e1 n) r'

theorem PPow_base {p : BHist} :
    UnaryHistory p -> PPow p BHist.Empty NatOne := by
  intro hp
  exact PPow.zero hp

theorem PPow_succ {p n r r' : BHist} :
    PPow p n r -> NatMul p r r' -> PPow p (BHist.e1 n) r' := by
  intro pow mul
  exact PPow.succ pow mul

theorem PPow_prime_unary {p n r : BHist} :
    PPow p n r -> UnaryHistory p := by
  intro pow
  induction pow with
  | zero hp =>
      exact hp
  | succ _pow _mul ih =>
      exact ih

theorem PPow_exponent_unary {p n r : BHist} :
    PPow p n r -> UnaryHistory n := by
  intro pow
  induction pow with
  | zero _hp =>
      exact unary_empty
  | succ _pow _mul ih =>
      exact unary_e1_closed ih

theorem PPow_result_unary {p n r : BHist} :
    PPow p n r -> UnaryHistory r := by
  intro pow
  induction pow with
  | zero _hp =>
      exact unary_e1_closed unary_empty
  | succ _pow mul ih =>
      exact NatMul_result_unary (NatMul_left_unary mul) mul

theorem PPow_total {p n : BHist} :
    UnaryHistory p -> UnaryHistory n ->
      ∃ r : BHist, UnaryHistory r ∧ PPow p n r := by
  intro hp hn
  induction n with
  | Empty =>
      exact ⟨NatOne, unary_e1_closed unary_empty, PPow.zero hp⟩
  | e0 n _ih =>
      cases hn
  | e1 n ih =>
      have prev := ih (unary_e1_inversion hn)
      cases prev with
      | intro r rData =>
          have next := NatMul_total hp rData.left
          cases next with
          | intro r' nextData =>
              exact ⟨r', nextData.left, PPow.succ rData.right nextData.right⟩

theorem PPow_functional {p n r s : BHist} :
    PPow p n r -> PPow p n s -> hsame r s := by
  intro left
  induction left generalizing s with
  | zero _hp =>
      intro right
      cases right with
      | zero _hpRight =>
          rfl
  | succ _leftPrev leftMul ih =>
      intro right
      cases right with
      | succ rightPrev rightMul =>
          have prevSame : hsame _ _ := ih rightPrev
          cases prevSame
          exact NatMul_functional (NatMul_left_unary leftMul) leftMul rightMul

theorem PPow_one {p r : BHist} :
    PPow p NatOne r -> hsame r p := by
  intro pow
  cases pow with
  | succ previous mul =>
      cases previous with
      | zero _hp =>
          exact NatMul_unit_right_hsame mul

theorem PPow_one_construct {p : BHist} :
    UnaryHistory p -> PPow p NatOne p := by
  intro hp
  exact PPow.succ (PPow.zero hp)
    (NatMul.succ (NatMul.zero hp) (cont_left_unit p))

theorem PPow_step_result {p n r r' : BHist} :
    PPow p n r -> NatMul p r r' -> PPow p (BHist.e1 n) r' :=
  PPow.succ

theorem PPow_succ_inversion {p n r' : BHist} :
    PPow p (BHist.e1 n) r' ->
      ∃ r : BHist, PPow p n r ∧ NatMul p r r' := by
  intro pow
  cases pow with
  | succ previous mul =>
      exact ⟨_, previous, mul⟩

theorem PPow_nonempty_result {p n r : BHist} :
    (hsame p BHist.Empty -> False) -> PPow p n r -> hsame r BHist.Empty -> False := by
  intro pNonempty pow
  induction pow with
  | zero _hp =>
      intro emptyResult
      exact not_hsame_e1_empty emptyResult
  | succ _prev mul ih =>
      intro emptyResult
      cases emptyResult
      have factorEmpty := NatMul_empty_result_factor_empty_or_multiplier_empty mul
      cases factorEmpty with
      | inl pEmpty =>
          exact pNonempty pEmpty
      | inr prevEmpty =>
          exact ih prevEmpty

def PDvdNat (p k n : BHist) : Prop :=
  ∃ pk : BHist, PPow p k pk ∧ NatDivides pk n

theorem PDvdNat_dividend_unary {p k n : BHist} :
    PDvdNat p k n -> UnaryHistory n := by
  intro h
  cases h with
  | intro _ data =>
      exact NatDivides_result_unary data.right

theorem PDvdNat_power_unary {p k n : BHist} :
    PDvdNat p k n -> UnaryHistory p ∧ UnaryHistory k := by
  intro h
  cases h with
  | intro _ data =>
      exact ⟨PPow_prime_unary data.left, PPow_exponent_unary data.left⟩

theorem PDvdNat_zero_power {p n : BHist} :
    UnaryHistory p -> UnaryHistory n -> PDvdNat p BHist.Empty n := by
  intro hp hn
  exact ⟨NatOne, PPow.zero hp, NatDivides_unit_left_iff.mpr hn⟩

theorem PDvdNat_succ_step {p k pk pkNext n : BHist} :
    PPow p k pk -> NatMul p pk pkNext -> NatDivides pkNext n ->
      PDvdNat p (BHist.e1 k) n := by
  intro pow step divides
  exact ⟨pkNext, PPow.succ pow step, divides⟩

theorem PDvdNat_succ_implies_current {p k n : BHist} :
    PDvdNat p (BHist.e1 k) n -> PDvdNat p k n := by
  intro dividesSucc
  cases dividesSucc with
  | intro pkNext data =>
      cases data with
      | intro powSucc dividesNext =>
          cases PPow_succ_inversion powSucc with
          | intro pk stepData =>
              have pkDividesNext : NatDivides pk pkNext :=
                NatDivides_mul_right_closed (PPow_prime_unary stepData.left)
                  (PPow_result_unary stepData.left) stepData.right
              exact ⟨pk, stepData.left, NatDivides_transitive pkDividesNext dividesNext⟩

theorem PDvdNat_exponent_hsame_transport {p k k' n : BHist} :
    PDvdNat p k n -> hsame k k' -> PDvdNat p k' n := by
  intro divides sameExponent
  cases sameExponent
  exact divides

theorem PDvdNat_cont_prefix_down {p k tail j n : BHist} :
    UnaryHistory tail -> Cont k tail j -> PDvdNat p j n -> PDvdNat p k n := by
  intro tailUnary tailCont divides
  induction tail generalizing j with
  | Empty =>
      exact PDvdNat_exponent_hsame_transport divides tailCont
  | e0 _tail _ih =>
      cases tailUnary
  | e1 tail ih =>
      have innerUnary : UnaryHistory tail := unary_e1_inversion tailUnary
      have dividesPred : PDvdNat p (append k tail) n := by
        have shifted : PDvdNat p (BHist.e1 (append k tail)) n :=
          PDvdNat_exponent_hsame_transport divides tailCont
        exact PDvdNat_succ_implies_current shifted
      exact ih innerUnary (cont_intro rfl) dividesPred

def IsPadicValNat (p n k : BHist) : Prop :=
  PDvdNat p k n ∧ (PDvdNat p (BHist.e1 k) n -> False)

theorem IsPadicValNat_divides {p n k : BHist} :
    IsPadicValNat p n k -> PDvdNat p k n := by
  intro h
  exact h.left

theorem IsPadicValNat_not_succ {p n k : BHist} :
    IsPadicValNat p n k -> PDvdNat p (BHist.e1 k) n -> False := by
  intro h
  exact h.right

theorem IsPadicValNat_zero_of_not_p_dvd {p n : BHist} :
    UnaryHistory p -> UnaryHistory n -> (NatDivides p n -> False) ->
      IsPadicValNat p n BHist.Empty := by
  intro hp hn notDivides
  constructor
  · exact PDvdNat_zero_power hp hn
  · intro succDivides
    cases succDivides with
    | intro pOne data =>
        cases data with
        | intro powOne divides =>
            have samePower : hsame pOne p := PPow_one powOne
            have shifted := NatDivides_divisor_hsame_transport divides samePower
            exact notDivides shifted.right

theorem IsPadicValNat_succ_unique_absurd {p n k : BHist} :
    IsPadicValNat p n k -> IsPadicValNat p n (BHist.e1 k) -> False := by
  intro current next
  exact current.right next.left

theorem IsPadicValNat_unique {p n k l : BHist} :
    IsPadicValNat p n k -> IsPadicValNat p n l -> hsame k l := by
  intro left right
  have kUnary : UnaryHistory k := (PDvdNat_power_unary left.left).right
  have lUnary : UnaryHistory l := (PDvdNat_power_unary right.left).right
  have trichotomy := NatUnaryPrefix_trichotomy_hsame_strict kUnary lUnary
  cases trichotomy with
  | inl same =>
      exact same
  | inr strictCases =>
      cases strictCases with
      | inl strictKL =>
          cases strictKL with
          | intro tail tailData =>
              cases tailData with
              | intro tailUnary tailRest =>
                  cases tailRest with
                  | intro tailNonempty tailCont =>
                      cases tail with
                      | Empty =>
                          exact False.elim (tailNonempty rfl)
                      | e0 _tail =>
                          cases tailUnary
                      | e1 tail =>
                          have innerUnary : UnaryHistory tail := unary_e1_inversion tailUnary
                          have succCont : Cont (BHist.e1 k) tail l := by
                            exact cont_intro
                              (tailCont.trans
                                (unary_append_e1_left (h := tail) (k := k) innerUnary).symm)
                          have succDivides : PDvdNat p (BHist.e1 k) n :=
                            PDvdNat_cont_prefix_down innerUnary succCont right.left
                          exact False.elim (left.right succDivides)
      | inr strictLK =>
          cases strictLK with
          | intro tail tailData =>
              cases tailData with
              | intro tailUnary tailRest =>
                  cases tailRest with
                  | intro tailNonempty tailCont =>
                      cases tail with
                      | Empty =>
                          exact False.elim (tailNonempty rfl)
                      | e0 _tail =>
                          cases tailUnary
                      | e1 tail =>
                          have innerUnary : UnaryHistory tail := unary_e1_inversion tailUnary
                          have succCont : Cont (BHist.e1 l) tail k := by
                            exact cont_intro
                              (tailCont.trans
                                (unary_append_e1_left (h := tail) (k := l) innerUnary).symm)
                          have succDivides : PDvdNat p (BHist.e1 l) n :=
                            PDvdNat_cont_prefix_down innerUnary succCont left.left
                          exact False.elim (right.right succDivides)

def PLocalMaximalNat (p n k : BHist) : Prop :=
  IsPadicValNat p n k

theorem IsPadicValNat_to_PLocalMaximalNat {p n k : BHist} :
    IsPadicValNat p n k -> PLocalMaximalNat p n k := by
  intro val
  exact val

def PDvdInt (p k : BHist) (z : BEDC.FKernel.Mark.BMark × BHist) : Prop :=
  IntCarrier z.1 z.2 ∧ PDvdNat p k z.2

def IsPadicValInt (p : BHist) (z : BEDC.FKernel.Mark.BMark × BHist) (k : BHist) :
    Prop :=
  IntCarrier z.1 z.2 ∧ IsPadicValNat p z.2 k

theorem IsPadicValInt_zero_of_not_p_dvd {p : BHist}
    {z : BEDC.FKernel.Mark.BMark × BHist} :
    IntCarrier z.1 z.2 -> (NatDivides p z.2 -> False) ->
      UnaryHistory p -> IsPadicValInt p z BHist.Empty := by
  intro carrier notDivides hp
  exact ⟨carrier, IsPadicValNat_zero_of_not_p_dvd hp carrier.right notDivides⟩

def PDvdIntPair (p k : BHist) (z : BHist × BHist) : Prop :=
  IntPairCarrier z.1 z.2 ∧ PDvdNat p k z.1 ∧ PDvdNat p k z.2

def IsPadicValIntPair (p : BHist) (z : BHist × BHist) (k : BHist) : Prop :=
  IntPairCarrier z.1 z.2 ∧ IsPadicValNat p z.1 k ∧ IsPadicValNat p z.2 k

theorem IsPadicValIntPair_components {p : BHist} {z : BHist × BHist} {k : BHist} :
    IsPadicValIntPair p z k ->
      IsPadicValNat p z.1 k ∧ IsPadicValNat p z.2 k := by
  intro h
  exact ⟨h.right.left, h.right.right⟩
end BEDC.Derived.PadicUp

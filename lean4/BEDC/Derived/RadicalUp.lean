import BEDC.Derived.ArithmeticFnUp

namespace BEDC.Derived.RadicalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp
open BEDC.Derived.ArithmeticFnUp

def radicalFactors : List BHist -> List BHist
  | [] => []
  | p :: ps =>
      if listContainsPrime p ps then radicalFactors ps else p :: radicalFactors ps

def radicalProduct (entries : List BHist) : BHist :=
  factorListProductFn (radicalFactors entries)

def RadicalOfFactorization (n r : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame (radicalProduct entries) r

def rad (n r : BHist) : Prop :=
  RadicalOfFactorization n r

def SquarefreeOfFactorization (n : BHist) : Prop :=
  ∃ entries : List BHist, PrimeFactorization n entries ∧ listSquarefree entries

private theorem radicalFactors_unfold (entries : List BHist) :
    radicalFactors entries =
      match entries with
      | [] => []
      | q :: qs =>
          if listContainsPrime q qs = true then radicalFactors qs
          else q :: radicalFactors qs := by
  cases entries <;> rfl

private theorem listContainsPrime_append_false {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = false -> listContainsPrime p ys = false ->
        listContainsPrime p (xs ++ ys) = false := by
  intro xs
  induction xs with
  | nil =>
      intro ys _leftAbsent rightAbsent
      exact rightAbsent
  | cons q qs ih =>
      intro ys leftAbsent rightAbsent
      change (if p = q then true else listContainsPrime p qs) = false at leftAbsent
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = false
      by_cases same : p = q
      · rw [if_pos same] at leftAbsent
        cases leftAbsent
      · rw [if_neg same] at leftAbsent
        rw [if_neg same]
        exact ih ys leftAbsent rightAbsent

private theorem listContainsPrime_append_true_left {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = true -> listContainsPrime p (xs ++ ys) = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys found
      cases found
  | cons q qs ih =>
      intro ys found
      change (if p = q then true else listContainsPrime p qs) = true at found
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = true
      by_cases same : p = q
      · rw [if_pos same]
      · rw [if_neg same] at found
        rw [if_neg same]
        exact ih ys found

private theorem listContainsPrime_perm_false {p : BHist} {xs ys : List BHist} :
    List.Perm xs ys -> listContainsPrime p xs = false ->
      listContainsPrime p ys = false := by
  intro perm
  induction perm with
  | nil =>
      intro _absent
      rfl
  | cons q perm ih =>
      intro absent
      change (if p = q then true else listContainsPrime p _) = false at absent
      change (if p = q then true else listContainsPrime p _) = false
      by_cases same : p = q
      · rw [if_pos same] at absent
        cases absent
      · rw [if_neg same] at absent
        rw [if_neg same]
        exact ih absent
  | swap q r zs =>
      intro absent
      change (if p = r then true else if p = q then true else listContainsPrime p zs) =
        false at absent
      change (if p = q then true else if p = r then true else listContainsPrime p zs) =
        false
      by_cases sameQ : p = q
      · by_cases sameR : p = r
        · rw [if_pos sameR] at absent
          cases absent
        · rw [if_neg sameR] at absent
          rw [if_pos sameQ] at absent
          cases absent
      · rw [if_neg sameQ] at absent
        rw [if_neg sameQ]
        by_cases sameR : p = r
        · rw [if_pos sameR] at absent
          cases absent
        · rw [if_neg sameR] at absent
          rw [if_neg sameR]
          exact absent
  | trans left right ihLeft ihRight =>
      intro absent
      exact ihRight (ihLeft absent)

private theorem listContainsPrime_cons_false {p q : BHist} {xs : List BHist} :
    listContainsPrime p (q :: xs) = false ->
      (p = q -> False) ∧ listContainsPrime p xs = false := by
  intro absent
  change (if p = q then true else listContainsPrime p xs) = false at absent
  constructor
  · intro same
    rw [if_pos same] at absent
    cases absent
  · by_cases same : p = q
    · rw [if_pos same] at absent
      cases absent
    · rw [if_neg same] at absent
      exact absent

theorem listSquarefree_perm {xs ys : List BHist} :
    List.Perm xs ys -> listSquarefree xs -> listSquarefree ys := by
  intro perm
  induction perm with
  | nil =>
      intro _squarefree
      trivial
  | cons p perm ih =>
      intro squarefree
      change listSquarefree (p :: _) at squarefree
      change listSquarefree (p :: _)
      constructor
      · exact listContainsPrime_perm_false perm squarefree.left
      · exact ih squarefree.right
  | swap p q xs =>
      intro squarefree
      change listSquarefree (q :: p :: xs) at squarefree
      change listSquarefree (p :: q :: xs)
      constructor
      · change (if p = q then true else listContainsPrime p xs) = false
        by_cases samePQ : p = q
        · have sameQP : q = p := samePQ.symm
          have headAbsent := squarefree.left
          change (if q = p then true else listContainsPrime q xs) = false at headAbsent
          rw [if_pos sameQP] at headAbsent
          cases headAbsent
        · rw [if_neg samePQ]
          exact squarefree.right.left
      · constructor
        · exact (listContainsPrime_cons_false squarefree.left).right
        · exact squarefree.right.right
  | trans left right ihLeft ihRight =>
      intro squarefree
      exact ihRight (ihLeft squarefree)

private theorem radicalFactors_length_le :
    ∀ entries : List BHist, (radicalFactors entries).length ≤ entries.length
  | [] =>
      Nat.le_refl 0
  | p :: ps => by
      unfold radicalFactors
      by_cases found : listContainsPrime p ps = true
      · rw [found]
        exact Nat.le_trans (radicalFactors_length_le ps) (Nat.le_succ ps.length)
      · have absent : listContainsPrime p ps = false := by
          cases h : listContainsPrime p ps
          · rfl
          · exact False.elim (found h)
        rw [absent]
        exact Nat.succ_le_succ (radicalFactors_length_le ps)

private theorem radicalFactors_absent_of_absent {p : BHist} :
    ∀ entries : List BHist,
      listContainsPrime p entries = false ->
        listContainsPrime p (radicalFactors entries) = false
  | [], _absent =>
      rfl
  | q :: qs, absent => by
      unfold radicalFactors
      have absentParts := listContainsPrime_cons_false absent
      by_cases found : listContainsPrime q qs = true
      · rw [found]
        exact radicalFactors_absent_of_absent qs absentParts.right
      · have qAbsent : listContainsPrime q qs = false := by
          cases h : listContainsPrime q qs
          · rfl
          · exact False.elim (found h)
        rw [qAbsent]
        change (if p = q then true else listContainsPrime p (radicalFactors qs)) = false
        rw [if_neg absentParts.left]
        exact radicalFactors_absent_of_absent qs absentParts.right

theorem radicalFactors_squarefree :
    ∀ entries : List BHist, listSquarefree (radicalFactors entries)
  | [] =>
      trivial
  | p :: ps => by
      unfold radicalFactors
      by_cases found : listContainsPrime p ps = true
      · rw [found]
        exact radicalFactors_squarefree ps
      · have absent : listContainsPrime p ps = false := by
          cases h : listContainsPrime p ps
          · rfl
          · exact False.elim (found h)
        rw [absent]
        change listSquarefree (p :: radicalFactors ps)
        constructor
        · exact radicalFactors_absent_of_absent ps absent
        · exact radicalFactors_squarefree ps

theorem radicalFactors_of_squarefree :
    ∀ entries : List BHist, listSquarefree entries -> radicalFactors entries = entries
  | [], _squarefree =>
      rfl
  | p :: ps, squarefree => by
      change listContainsPrime p ps = false ∧ listSquarefree ps at squarefree
      unfold radicalFactors
      rw [squarefree.left]
      exact congrArg (fun tail => p :: tail)
        (radicalFactors_of_squarefree ps squarefree.right)

theorem radicalFactors_eq_self_iff (entries : List BHist) :
    listSquarefree entries ↔ radicalFactors entries = entries := by
  constructor
  · intro squarefree
    exact radicalFactors_of_squarefree entries squarefree
  · intro fixed
    induction entries with
    | nil =>
        trivial
    | cons p ps ih =>
        unfold radicalFactors at fixed
        by_cases found : listContainsPrime p ps = true
        · rw [found] at fixed
          change radicalFactors ps = p :: ps at fixed
          have lengthEq := congrArg List.length fixed
          have leftLe : (radicalFactors ps).length ≤ ps.length :=
            radicalFactors_length_le ps
          have impossible : ps.length.succ ≤ ps.length := by
            change (radicalFactors ps).length = Nat.succ ps.length at lengthEq
            rw [lengthEq] at leftLe
            exact leftLe
          exact False.elim (Nat.not_succ_le_self ps.length impossible)
        · have absent : listContainsPrime p ps = false := by
            cases h : listContainsPrime p ps
            · rfl
            · exact False.elim (found h)
          rw [absent] at fixed
          injection fixed with _headFixed tailFixed
          change listSquarefree (p :: ps)
          exact ⟨absent, ih tailFixed⟩

private theorem factorListProductFn_unary_of_product {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n -> UnaryHistory (factorListProductFn entries) := by
  intro product
  induction entries generalizing n with
  | nil =>
      unfold factorListProductFn
      exact unary_e1_closed unary_empty
  | cons p ps ih =>
      cases product with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold factorListProductFn
              exact natMulFn_unary pPrime.left (ih tailData.left)

theorem factorListProductFn_hsame_of_product {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n -> hsame (factorListProductFn entries) n := by
  intro product
  induction entries generalizing n with
  | nil =>
      unfold factorListProductFn
      exact hsame_symm product
  | cons p ps ih =>
      cases product with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold factorListProductFn
              have tailUnary : UnaryHistory (factorListProductFn ps) :=
                factorListProductFn_unary_of_product tailData.left
              have raw : NatMul p (factorListProductFn ps)
                  (natMulFn p (factorListProductFn ps)) :=
                natMulFn_rel pPrime.left tailUnary
              have shifted : NatMul p tailProduct (natMulFn p (factorListProductFn ps)) :=
                (NatMul_multiplier_hsame_transport raw (ih tailData.left)).right
              exact NatMul_functional pPrime.left shifted tailData.right

theorem radicalProduct_factorization_product {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n ->
      PrimeFactorizationProduct (radicalFactors entries) (radicalProduct entries) := by
  intro product
  induction entries generalizing n with
  | nil =>
      unfold radicalProduct radicalFactors factorListProductFn
      exact hsame_refl NatOne
  | cons p ps ih =>
      cases product with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold radicalProduct radicalFactors
              by_cases found : listContainsPrime p ps = true
              · rw [found]
                exact ih tailData.left
              · have absent : listContainsPrime p ps = false := by
                  cases h : listContainsPrime p ps
                  · rfl
                  · exact False.elim (found h)
                rw [absent]
                unfold factorListProductFn
                have tailProductProof :
                    PrimeFactorizationProduct (radicalFactors ps) (radicalProduct ps) :=
                  ih tailData.left
                have tailUnary : UnaryHistory (radicalProduct ps) :=
                  PrimeFactorizationProduct_result_unary tailProductProof
                exact ⟨pPrime, radicalProduct ps, tailProductProof,
                  natMulFn_rel pPrime.left tailUnary⟩

theorem RadicalOfFactorization_self {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries -> RadicalOfFactorization n (radicalProduct entries) := by
  intro factorization
  exact ⟨entries, factorization, hsame_refl (radicalProduct entries)⟩

theorem radical_divides_factorization_product {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n -> NatDivides (radicalProduct entries) n := by
  intro product
  induction entries generalizing n with
  | nil =>
      unfold radicalProduct radicalFactors factorListProductFn
      have nUnary : UnaryHistory n := PrimeFactorizationProduct_result_unary product
      have unitDividesN := (NatDivides_reflexive_pair nUnary).left
      exact unitDividesN
  | cons p ps ih =>
      cases product with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold radicalProduct radicalFactors
              by_cases found : listContainsPrime p ps = true
              · rw [found]
                exact NatDivides_mul_left_closed pPrime.left (ih tailData.left)
                  tailData.right
              · have absent : listContainsPrime p ps = false := by
                  cases h : listContainsPrime p ps
                  · rfl
                  · exact False.elim (found h)
                rw [absent]
                unfold factorListProductFn
                have tailRadProduct :
                    PrimeFactorizationProduct (radicalFactors ps) (radicalProduct ps) :=
                  radicalProduct_factorization_product tailData.left
                have tailRadUnary : UnaryHistory (radicalProduct ps) :=
                  PrimeFactorizationProduct_result_unary tailRadProduct
                have productDE : NatMul p (radicalProduct ps)
                    (natMulFn p (radicalProduct ps)) :=
                  natMulFn_rel pPrime.left tailRadUnary
                exact NatDivides_product_closed pPrime.left tailRadUnary pPrime.left
                  (PrimeFactorizationProduct_result_unary tailData.left)
                  (NatDivides_reflexive_pair pPrime.left).right (ih tailData.left)
                  productDE tailData.right

theorem radical_divides {n r : BHist} :
    RadicalOfFactorization n r -> NatDivides r n := by
  intro radical
  cases radical with
  | intro entries data =>
      have divides : NatDivides (radicalProduct entries) n :=
        radical_divides_factorization_product data.left.right
      exact (NatDivides_divisor_hsame_transport divides data.right).right

theorem radical_squarefree_iff {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n ->
      (hsame (radicalProduct entries) n ↔ listSquarefree entries) := by
  intro product
  constructor
  · intro sameRad
    have radicalProductProof :
        PrimeFactorizationProduct (radicalFactors entries) (radicalProduct entries) :=
      radicalProduct_factorization_product product
    have radicalAtN :
        PrimeFactorizationProduct (radicalFactors entries) n :=
      PrimeFactorizationProduct_result_hsame_transport radicalProductProof sameRad
    have perm : ListPermPrime (radicalFactors entries) entries :=
      factorization_unique_perm radicalAtN product
    exact listSquarefree_perm perm (radicalFactors_squarefree entries)
  · intro squarefree
    unfold radicalProduct
    rw [radicalFactors_of_squarefree entries squarefree]
    exact factorListProductFn_hsame_of_product product

theorem rad_self_iff_squarefree {n : BHist} :
    RadicalOfFactorization n n ↔ SquarefreeOfFactorization n := by
  constructor
  · intro radical
    cases radical with
    | intro entries data =>
        exact ⟨entries, data.left,
          (radical_squarefree_iff data.left.right).mp data.right⟩
  · intro squarefree
    cases squarefree with
    | intro entries data =>
        exact ⟨entries, data.left,
          (radical_squarefree_iff data.left.right).mpr data.right⟩

theorem radicalFactors_append_disjoint :
    ∀ xs ys : List BHist,
      listNoCommonPrime xs ys ->
        radicalFactors (xs ++ ys) = radicalFactors xs ++ radicalFactors ys
  | [], ys, _common =>
      rfl
  | p :: ps, ys, common => by
      change listContainsPrime p ys = false ∧ listNoCommonPrime ps ys at common
      change radicalFactors (p :: (ps ++ ys)) =
        radicalFactors (p :: ps) ++ radicalFactors ys
      unfold radicalFactors
      by_cases foundPs : listContainsPrime p ps = true
      · have foundAppend : listContainsPrime p (ps ++ ys) = true :=
          listContainsPrime_append_true_left ps ys foundPs
        rw [foundAppend, foundPs]
        have ysUnfold := radicalFactors_unfold ys
        exact (radicalFactors_append_disjoint ps ys common.right).trans
          (congrArg (fun tail => radicalFactors ps ++ tail) ysUnfold)
      · have absentPs : listContainsPrime p ps = false := by
          cases h : listContainsPrime p ps
          · rfl
          · exact False.elim (foundPs h)
        have absentAppend : listContainsPrime p (ps ++ ys) = false :=
          listContainsPrime_append_false ps ys absentPs common.left
        rw [absentAppend, absentPs]
        have ysUnfold := radicalFactors_unfold ys
        exact congrArg (fun tail => p :: tail)
          ((radicalFactors_append_disjoint ps ys common.right).trans
            (congrArg (fun tail => radicalFactors ps ++ tail) ysUnfold))

theorem radicalProduct_append_disjoint_hsame
    {xs ys : List BHist} {m n : BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        listNoCommonPrime xs ys ->
          hsame (radicalProduct (xs ++ ys))
            (natMulFn (radicalProduct xs) (radicalProduct ys)) := by
  intro fx fy common
  have rxProduct :
      PrimeFactorizationProduct (radicalFactors xs) (radicalProduct xs) :=
    radicalProduct_factorization_product fx
  have ryProduct :
      PrimeFactorizationProduct (radicalFactors ys) (radicalProduct ys) :=
    radicalProduct_factorization_product fy
  have rxUnary : UnaryHistory (radicalProduct xs) :=
    PrimeFactorizationProduct_result_unary rxProduct
  have ryUnary : UnaryHistory (radicalProduct ys) :=
    PrimeFactorizationProduct_result_unary ryProduct
  have productMul : NatMul (radicalProduct xs) (radicalProduct ys)
      (natMulFn (radicalProduct xs) (radicalProduct ys)) :=
    natMulFn_rel rxUnary ryUnary
  have appendProduct :
      PrimeFactorizationProduct (radicalFactors xs ++ radicalFactors ys)
        (natMulFn (radicalProduct xs) (radicalProduct ys)) :=
    PrimeFactorizationProduct_append_mul rxProduct ryProduct productMul
  unfold radicalProduct
  rw [radicalFactors_append_disjoint xs ys common]
  exact factorListProductFn_hsame_of_product appendProduct

theorem radical_multiplicative
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorization m xs ->
      PrimeFactorization n ys ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            RadicalOfFactorization mn
              (natMulFn (radicalProduct xs) (radicalProduct ys)) := by
  intro fx fy productMN gcd
  have common : listNoCommonPrime xs ys :=
    PrimeFactorizationProduct_coprime_no_common fx.right fy.right gcd
  have productFactors :
      PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx.right fy.right productMN
  have mnUnary : UnaryHistory mn := NatMul_result_unary fx.left productMN
  exact ⟨xs ++ ys, ⟨mnUnary, productFactors⟩,
    radicalProduct_append_disjoint_hsame fx.right fy.right common⟩

theorem rad_multiplicative_rel
    {m n mn rm rn : BHist} :
    RadicalOfFactorization m rm ->
      RadicalOfFactorization n rn ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            RadicalOfFactorization mn (natMulFn rm rn) := by
  intro rmRad rnRad productMN gcd
  cases rmRad with
  | intro xs xData =>
      cases rnRad with
      | intro ys yData =>
          have base :
              RadicalOfFactorization mn
                (natMulFn (radicalProduct xs) (radicalProduct ys)) :=
            radical_multiplicative xData.left yData.left productMN gcd
          have rxProduct :
              PrimeFactorizationProduct (radicalFactors xs) (radicalProduct xs) :=
            radicalProduct_factorization_product xData.left.right
          have ryProduct :
              PrimeFactorizationProduct (radicalFactors ys) (radicalProduct ys) :=
            radicalProduct_factorization_product yData.left.right
          have rxUnary : UnaryHistory (radicalProduct xs) :=
            PrimeFactorizationProduct_result_unary rxProduct
          have ryUnary : UnaryHistory (radicalProduct ys) :=
            PrimeFactorizationProduct_result_unary ryProduct
          have rmUnary : UnaryHistory rm :=
            unary_transport rxUnary xData.right
          have rnUnary : UnaryHistory rn :=
            unary_transport ryUnary yData.right
          have rawMul : NatMul (radicalProduct xs) (radicalProduct ys)
              (natMulFn (radicalProduct xs) (radicalProduct ys)) :=
            natMulFn_rel rxUnary ryUnary
          have shiftedMul : NatMul rm rn
              (natMulFn (radicalProduct xs) (radicalProduct ys)) :=
            (NatMul_operation_congruence rawMul xData.right yData.right
              (hsame_refl _)).left
          have targetMul : NatMul rm rn (natMulFn rm rn) :=
            natMulFn_rel rmUnary rnUnary
          have sameProducts :
              hsame (natMulFn (radicalProduct xs) (radicalProduct ys))
                (natMulFn rm rn) :=
            NatMul_functional rmUnary shiftedMul targetMul
          cases base with
          | intro entries baseData =>
              exact ⟨entries, baseData.left,
                hsame_trans baseData.right sameProducts⟩

end BEDC.Derived.RadicalUp

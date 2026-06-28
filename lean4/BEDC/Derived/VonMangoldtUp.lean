import BEDC.Derived.MobiusInversionUp

namespace BEDC.Derived.VonMangoldtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.PrimeUp

/-!
`FormalLog` 是素因子日志的有限符号和。`[]` 表示零，
`[p]` 表示一个未赋值的 `log p` token，拼接表示有限加法。
这里不声称实数对数或有理逼近已经构造完成。
-/

abbrev FormalLog := List BHist

def formalLogZero : FormalLog := []

def formalLogPrime (p : BHist) : FormalLog := [p]

def formalLogAdd (x y : FormalLog) : FormalLog := x ++ y

def FormalLogEq (x y : FormalLog) : Prop :=
  ∀ p : BHist, listPrimeCountNat p x = listPrimeCountNat p y

def allEqualPrime (p : BHist) : List BHist -> Bool
  | [] => true
  | q :: qs =>
      if q = p then allEqualPrime p qs else false

def vonMangoldtFactorList : List BHist -> FormalLog
  | [] => formalLogZero
  | p :: ps =>
      if allEqualPrime p ps then formalLogPrime p else formalLogZero

def sumVonMangoldtFactorLists : List (List BHist) -> FormalLog
  | [] => formalLogZero
  | fs :: fss =>
      formalLogAdd (vonMangoldtFactorList fs)
        (sumVonMangoldtFactorLists fss)

def primePowerDivisorFactorRows (p : BHist) : Nat -> List (List BHist)
  | 0 => []
  | k + 1 =>
      repeatPrimeFactor p (k + 1) :: primePowerDivisorFactorRows p k

def groupedPrimeLogAux : List BHist -> List BHist -> FormalLog
  | _seen, [] => []
  | seen, p :: ps =>
      if listContainsPrime p seen then groupedPrimeLogAux seen ps
      else repeatPrimeFactor p (listPrimeCountNat p ps + 1) ++
        groupedPrimeLogAux (p :: seen) ps

def groupedPrimeLog (entries : List BHist) : FormalLog :=
  groupedPrimeLogAux [] entries

def nonzeroVonMangoldtDivisorFactorListsAux :
    List BHist -> List BHist -> List (List BHist)
  | _seen, [] => []
  | seen, p :: ps =>
      if listContainsPrime p seen then
        nonzeroVonMangoldtDivisorFactorListsAux seen ps
      else
        primePowerDivisorFactorRows p (listPrimeCountNat p ps + 1) ++
          nonzeroVonMangoldtDivisorFactorListsAux (p :: seen) ps

def nonzeroVonMangoldtDivisorFactorLists
    (entries : List BHist) : List (List BHist) :=
  nonzeroVonMangoldtDivisorFactorListsAux [] entries

def sumVonMangoldtNonzeroDivisorFactorLists
    (entries : List BHist) : FormalLog :=
  sumVonMangoldtFactorLists
    (nonzeroVonMangoldtDivisorFactorLists entries)

def VonMangoldtOfFactorization
    (n : BHist) (value : FormalLog) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ value = vonMangoldtFactorList entries

def VonMangoldtNonzeroDivisorSumOfFactorization
    (n : BHist) (value : FormalLog) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧
      value = sumVonMangoldtNonzeroDivisorFactorLists entries ∧
        FormalLogEq value entries

theorem formalLogEq_refl (x : FormalLog) : FormalLogEq x x := by
  intro p
  rfl

theorem allEqualPrime_repeat (p : BHist) :
    ∀ k : Nat, allEqualPrime p (repeatPrimeFactor p k) = true
  | 0 => rfl
  | k + 1 => by
      change (if p = p then allEqualPrime p (repeatPrimeFactor p k)
        else false) = true
      rw [if_pos rfl]
      exact allEqualPrime_repeat p k

theorem vonMangoldtFactorList_empty :
    vonMangoldtFactorList [] = formalLogZero := by
  rfl

theorem vonMangoldtFactorList_not_primePower
    {p : BHist} {ps : List BHist} :
    allEqualPrime p ps = false ->
      vonMangoldtFactorList (p :: ps) = formalLogZero := by
  intro notPower
  change (if allEqualPrime p ps then formalLogPrime p else formalLogZero) =
    formalLogZero
  rw [notPower]
  rfl

theorem vonMangoldtFactorList_repeatPrimeFactor
    (p : BHist) :
    ∀ k : Nat,
      vonMangoldtFactorList (repeatPrimeFactor p (k + 1)) =
        formalLogPrime p
  | 0 => by
      change (if allEqualPrime p [] then formalLogPrime p else formalLogZero) =
        formalLogPrime p
      rfl
  | k + 1 => by
      change
        (if allEqualPrime p (repeatPrimeFactor p (k + 1))
          then formalLogPrime p else formalLogZero) =
          formalLogPrime p
      rw [allEqualPrime_repeat p (k + 1)]
      rfl

theorem sumVonMangoldtFactorLists_append
    (xs ys : List (List BHist)) :
    sumVonMangoldtFactorLists (xs ++ ys) =
      sumVonMangoldtFactorLists xs ++ sumVonMangoldtFactorLists ys := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change
        vonMangoldtFactorList x ++
            sumVonMangoldtFactorLists (xs ++ ys) =
          (vonMangoldtFactorList x ++ sumVonMangoldtFactorLists xs) ++
            sumVonMangoldtFactorLists ys
      rw [ih]
      induction vonMangoldtFactorList x with
      | nil =>
          rfl
      | cons _ _ tailAssoc =>
          exact congrArg (fun rest => _ :: rest) tailAssoc

theorem sumVonMangoldt_primePowerDivisorFactorRows
    (p : BHist) :
    ∀ k : Nat,
      sumVonMangoldtFactorLists (primePowerDivisorFactorRows p k) =
        repeatPrimeFactor p k
  | 0 => rfl
  | k + 1 => by
      change
        vonMangoldtFactorList (repeatPrimeFactor p (k + 1)) ++
          sumVonMangoldtFactorLists (primePowerDivisorFactorRows p k) =
          repeatPrimeFactor p (k + 1)
      rw [vonMangoldtFactorList_repeatPrimeFactor p k]
      rw [sumVonMangoldt_primePowerDivisorFactorRows p k]
      rfl

theorem sumVonMangoldt_nonzeroDivisorFactorListsAux
    (seen entries : List BHist) :
    sumVonMangoldtFactorLists
      (nonzeroVonMangoldtDivisorFactorListsAux seen entries) =
        groupedPrimeLogAux seen entries := by
  induction entries generalizing seen with
  | nil =>
      rfl
  | cons p ps ih =>
      unfold nonzeroVonMangoldtDivisorFactorListsAux groupedPrimeLogAux
      cases present : listContainsPrime p seen
      · change
          sumVonMangoldtFactorLists
            (primePowerDivisorFactorRows p (listPrimeCountNat p ps + 1) ++
              nonzeroVonMangoldtDivisorFactorListsAux (p :: seen) ps) =
            repeatPrimeFactor p (listPrimeCountNat p ps + 1) ++
              groupedPrimeLogAux (p :: seen) ps
        rw [sumVonMangoldtFactorLists_append]
        rw [sumVonMangoldt_primePowerDivisorFactorRows]
        exact congrArg
          (fun tail =>
            repeatPrimeFactor p (listPrimeCountNat p ps + 1) ++ tail)
          (ih (p :: seen))
      · exact ih seen

theorem sumVonMangoldtNonzeroDivisorFactorLists_eq_grouped
    (entries : List BHist) :
    sumVonMangoldtNonzeroDivisorFactorLists entries =
      groupedPrimeLog entries := by
  unfold sumVonMangoldtNonzeroDivisorFactorLists
  unfold nonzeroVonMangoldtDivisorFactorLists
  unfold groupedPrimeLog
  exact sumVonMangoldt_nonzeroDivisorFactorListsAux [] entries

theorem listPrimeCountNat_append
    (p : BHist) :
    ∀ xs ys : List BHist,
      listPrimeCountNat p (xs ++ ys) =
        listPrimeCountNat p xs + listPrimeCountNat p ys
  | [], ys => (Nat.zero_add (listPrimeCountNat p ys)).symm
  | q :: qs, ys => by
      change
        (if p = q then listPrimeCountNat p (qs ++ ys) + 1
          else listPrimeCountNat p (qs ++ ys)) =
          (if p = q then listPrimeCountNat p qs + 1
            else listPrimeCountNat p qs) + listPrimeCountNat p ys
      by_cases same : p = q
      · rw [if_pos same]
        rw [if_pos same]
        rw [listPrimeCountNat_append p qs ys]
        calc
          listPrimeCountNat p qs + listPrimeCountNat p ys + 1 =
              listPrimeCountNat p qs + (listPrimeCountNat p ys + 1) :=
            Nat.add_assoc (listPrimeCountNat p qs) (listPrimeCountNat p ys) 1
          _ = listPrimeCountNat p qs + (1 + listPrimeCountNat p ys) :=
            congrArg (fun x => listPrimeCountNat p qs + x)
              (Nat.add_comm (listPrimeCountNat p ys) 1)
          _ = listPrimeCountNat p qs + 1 + listPrimeCountNat p ys :=
            (Nat.add_assoc (listPrimeCountNat p qs) 1
              (listPrimeCountNat p ys)).symm
      · rw [if_neg same]
        rw [if_neg same]
        exact listPrimeCountNat_append p qs ys

theorem listPrimeCountNat_repeat_same
    (p : BHist) :
    ∀ k : Nat, listPrimeCountNat p (repeatPrimeFactor p k) = k
  | 0 => rfl
  | k + 1 => by
      change
        (if p = p then listPrimeCountNat p (repeatPrimeFactor p k) + 1
          else listPrimeCountNat p (repeatPrimeFactor p k)) = k + 1
      rw [if_pos rfl]
      rw [listPrimeCountNat_repeat_same p k]

theorem listPrimeCountNat_repeat_ne
    {p q : BHist} :
    (p = q -> False) ->
      ∀ k : Nat, listPrimeCountNat p (repeatPrimeFactor q k) = 0
  | _ne, 0 => rfl
  | ne, k + 1 => by
      change
        (if p = q then listPrimeCountNat p (repeatPrimeFactor q k) + 1
          else listPrimeCountNat p (repeatPrimeFactor q k)) = 0
      rw [if_neg ne]
      exact listPrimeCountNat_repeat_ne ne k

theorem groupedPrimeLogAux_count_present_zero
    (p : BHist) :
    ∀ seen entries : List BHist,
      listContainsPrime p seen = true ->
        listPrimeCountNat p (groupedPrimeLogAux seen entries) = 0
  | seen, [], _present => rfl
  | seen, q :: qs, present => by
      unfold groupedPrimeLogAux
      cases qPresent : listContainsPrime q seen
      · change
          listPrimeCountNat p
            (repeatPrimeFactor q (listPrimeCountNat q qs + 1) ++
              groupedPrimeLogAux (q :: seen) qs) = 0
        rw [listPrimeCountNat_append]
        by_cases same : p = q
        · cases same
          rw [present] at qPresent
          cases qPresent
        · have pPresentTail : listContainsPrime p (q :: seen) = true := by
            change (if p = q then true else listContainsPrime p seen) = true
            rw [if_neg same]
            exact present
          rw [listPrimeCountNat_repeat_ne same]
          rw [groupedPrimeLogAux_count_present_zero p (q :: seen) qs pPresentTail]
      · exact groupedPrimeLogAux_count_present_zero p seen qs present

theorem groupedPrimeLogAux_count_absent
    (p : BHist) :
    ∀ seen entries : List BHist,
      listContainsPrime p seen = false ->
        listPrimeCountNat p (groupedPrimeLogAux seen entries) =
          listPrimeCountNat p entries
  | seen, [], _absent => rfl
  | seen, q :: qs, absent => by
      unfold groupedPrimeLogAux
      cases qPresent : listContainsPrime q seen
      · change
          listPrimeCountNat p
            (repeatPrimeFactor q (listPrimeCountNat q qs + 1) ++
              groupedPrimeLogAux (q :: seen) qs) =
            listPrimeCountNat p (q :: qs)
        rw [listPrimeCountNat_append]
        by_cases same : p = q
        · cases same
          rw [listPrimeCountNat_repeat_same]
          have pSeen : listContainsPrime p (p :: seen) = true := by
            change (if p = p then true else listContainsPrime p seen) = true
            rw [if_pos rfl]
          rw [groupedPrimeLogAux_count_present_zero p (p :: seen) qs pSeen]
          change listPrimeCountNat p qs + 1 + 0 =
            (if p = p then listPrimeCountNat p qs + 1
              else listPrimeCountNat p qs)
          rw [if_pos rfl]
        · have pAbsentTail : listContainsPrime p (q :: seen) = false := by
            change (if p = q then true else listContainsPrime p seen) = false
            rw [if_neg same]
            exact absent
          rw [listPrimeCountNat_repeat_ne same]
          rw [groupedPrimeLogAux_count_absent p (q :: seen) qs pAbsentTail]
          change 0 + listPrimeCountNat p qs =
            (if p = q then listPrimeCountNat p qs + 1
              else listPrimeCountNat p qs)
          rw [if_neg same]
          exact Nat.zero_add (listPrimeCountNat p qs)
      · change listPrimeCountNat p (groupedPrimeLogAux seen qs) =
          listPrimeCountNat p (q :: qs)
        rw [groupedPrimeLogAux_count_absent p seen qs absent]
        change listPrimeCountNat p qs =
          (if p = q then listPrimeCountNat p qs + 1
            else listPrimeCountNat p qs)
        have notSame : p = q -> False := by
          intro same
          cases same
          rw [qPresent] at absent
          cases absent
        rw [if_neg notSame]

theorem groupedPrimeLog_formalLogEq
    (entries : List BHist) :
    FormalLogEq (groupedPrimeLog entries) entries := by
  intro p
  unfold groupedPrimeLog
  exact groupedPrimeLogAux_count_absent p [] entries rfl

theorem sumVonMangoldtNonzeroDivisorFactorLists_formalLogEq
    (entries : List BHist) :
    FormalLogEq
      (sumVonMangoldtNonzeroDivisorFactorLists entries) entries := by
  intro p
  rw [sumVonMangoldtNonzeroDivisorFactorLists_eq_grouped]
  exact groupedPrimeLog_formalLogEq entries p

theorem vonMangoldt_primePower
    {n p : BHist} {k : Nat} :
    NatPrime p ->
      PrimeFactorizationProduct (repeatPrimeFactor p (k + 1)) n ->
        VonMangoldtOfFactorization n (formalLogPrime p) := by
  intro _pPrime product
  exact ⟨repeatPrimeFactor p (k + 1),
    ⟨PrimeFactorizationProduct_result_unary product, product⟩,
    (vonMangoldtFactorList_repeatPrimeFactor p k).symm⟩

theorem vonMangoldt_nonzeroDivisorSum_of_factorization
    {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      VonMangoldtNonzeroDivisorSumOfFactorization n
        (sumVonMangoldtNonzeroDivisorFactorLists entries) := by
  intro factorization
  exact ⟨entries, factorization, rfl,
    sumVonMangoldtNonzeroDivisorFactorLists_formalLogEq entries⟩

theorem vonMangoldt_primePower_divisorSum
    (p : BHist) (k : Nat) :
    sumVonMangoldtFactorLists (primePowerDivisorFactorRows p k) =
      repeatPrimeFactor p k :=
  sumVonMangoldt_primePowerDivisorFactorRows p k

end BEDC.Derived.VonMangoldtUp

import BEDC.Derived.GcdUp
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.ArithmeticFnUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp
open BEDC.Derived.RationalUp

def natPow (base exp : Nat) : Nat :=
  match exp with
  | 0 => 1
  | exp' + 1 => base * natPow base exp'

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

def listPrimeCountNat (p : BHist) : List BHist -> Nat
  | [] => 0
  | q :: qs =>
      if p = q then listPrimeCountNat p qs + 1 else listPrimeCountNat p qs

def listRemovePrime (p : BHist) : List BHist -> List BHist
  | [] => []
  | q :: qs => if p = q then listRemovePrime p qs else q :: listRemovePrime p qs

def listContainsPrime (p : BHist) : List BHist -> Bool
  | [] => false
  | q :: qs => if p = q then true else listContainsPrime p qs

def listNoCommonPrime : List BHist -> List BHist -> Prop
  | [], _ => True
  | p :: ps, qs => listContainsPrime p qs = false ∧ listNoCommonPrime ps qs

def listSquarefree : List BHist -> Prop
  | [] => True
  | p :: ps => listContainsPrime p ps = false ∧ listSquarefree ps

def eulerFactorNat (p : BHist) (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k' + 1 => natPow (bwordLength p) k' * (bwordLength p - 1)

def sigmaFactorNat (p : BHist) (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k' + 1 => sigmaFactorNat p k' + natPow (bwordLength p) (k' + 1)

def eulerPhiFactorsNat : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then bwordLength p * eulerPhiFactorsNat ps
      else (bwordLength p - 1) * eulerPhiFactorsNat ps

def sigmaFactorsNatFrom (entries : List BHist) : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then sigmaFactorsNatFrom entries ps
      else sigmaFactorNat p (listPrimeCountNat p entries) *
        sigmaFactorsNatFrom entries ps

def sigmaFactorsNat (entries : List BHist) : Nat :=
  sigmaFactorsNatFrom entries entries

def mobiusFactorsInt : List BHist -> _root_.Int
  | [] => 1
  | p :: ps => if listContainsPrime p ps then 0 else -mobiusFactorsInt ps

def mobiusFactorsIntegerUp : List BHist -> IntegerUp
  | [] => intOne
  | p :: ps =>
      if listContainsPrime p ps then intZero else IntNeg (mobiusFactorsIntegerUp ps)

def eulerPhiFactors (entries : List BHist) : BHist :=
  natToUnary (eulerPhiFactorsNat entries)

def sigmaFactors (entries : List BHist) : BHist :=
  natToUnary (sigmaFactorsNat entries)

def EulerPhiOfFactorization (n phi : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame phi (eulerPhiFactors entries)

def DivisorSigmaOfFactorization (n sigma : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame sigma (sigmaFactors entries)

def MobiusOfFactorization (n : BHist) (mu : _root_.Int) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ mu = mobiusFactorsInt entries

def NatCoprimeByGcd (m n : BHist) : Prop :=
  NatGcd m n NatOne

theorem eulerPhiFactors_unary (entries : List BHist) :
    UnaryHistory (eulerPhiFactors entries) := by
  unfold eulerPhiFactors
  exact natToUnary_unary _

theorem sigmaFactors_unary (entries : List BHist) :
    UnaryHistory (sigmaFactors entries) := by
  unfold sigmaFactors
  exact natToUnary_unary _

theorem mobiusFactorsInt_repeated_zero {p : BHist} {ps : List BHist} :
    listContainsPrime p ps = true -> mobiusFactorsInt (p :: ps) = 0 := by
  intro member
  change (if listContainsPrime p ps then 0 else -mobiusFactorsInt ps) = 0
  rw [member]
  rfl

theorem mobiusFactorsIntegerUp_repeated_zero {p : BHist} {ps : List BHist} :
    listContainsPrime p ps = true ->
      IntEq (mobiusFactorsIntegerUp (p :: ps)) intZero := by
  intro member
  change IntEq (if listContainsPrime p ps then intZero
    else IntNeg (mobiusFactorsIntegerUp ps)) intZero
  rw [member]
  exact IntEq_refl intZero

def repeatPrimeFactor (p : BHist) : Nat -> List BHist
  | 0 => []
  | k + 1 => p :: repeatPrimeFactor p k

def primePowerFactorLists (p : BHist) : Nat -> List (List BHist)
  | 0 => [[]]
  | k + 1 => [] :: (primePowerFactorLists p k).map (fun fs => p :: fs)

def appendFactorListProducts
    (left right : List (List BHist)) : List (List BHist) :=
  match right with
  | [] => []
  | r :: rs => left.map (fun l => l ++ r) ++ appendFactorListProducts left rs

def divisorFactorListsAux : List BHist -> List BHist -> List (List BHist)
  | _seen, [] => [[]]
  | seen, p :: ps =>
      if listContainsPrime p seen then divisorFactorListsAux seen ps
      else appendFactorListProducts
        (primePowerFactorLists p (listPrimeCountNat p ps + 1))
        (divisorFactorListsAux (p :: seen) ps)

def divisorFactorLists (entries : List BHist) : List (List BHist) :=
  divisorFactorListsAux [] entries

def factorListProductFn : List BHist -> BHist
  | [] => NatOne
  | p :: ps => natMulFn p (factorListProductFn ps)

def divisorProductsOfFactorization (entries : List BHist) : List BHist :=
  (divisorFactorLists entries).map factorListProductFn

def divisors (n : BHist) (ds : List BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ ds = divisorProductsOfFactorization entries

def integerUpListSum : List IntegerUp -> IntegerUp
  | [] => intZero
  | x :: xs => IntAdd x (integerUpListSum xs)

def mobiusFactorListSum : List (List BHist) -> IntegerUp
  | [] => intZero
  | fs :: fss => IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum fss)

def mobiusDivisorSumFactors (entries : List BHist) : IntegerUp :=
  mobiusFactorListSum (divisorFactorLists entries)

def mobiusIndicatorIntegerUp : List BHist -> IntegerUp
  | [] => intOne
  | _ :: _ => intZero

theorem divisorFactorLists_nil :
    divisorFactorLists ([] : List BHist) = [[]] := by
  rfl

theorem divisorFactorLists_cons (p : BHist) (ps : List BHist) :
    divisorFactorLists (p :: ps) =
      appendFactorListProducts
        (primePowerFactorLists p (listPrimeCountNat p ps + 1))
        (divisorFactorListsAux [p] ps) := by
  rfl

theorem divisors_of_factorization
    {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      divisors n (divisorProductsOfFactorization entries) := by
  intro factorization
  exact ⟨entries, factorization, rfl⟩

private theorem listRemovePrime_length_le (p : BHist) :
    ∀ xs : List BHist, (listRemovePrime p xs).length ≤ xs.length := by
  intro xs
  induction xs with
  | nil =>
      exact Nat.le_refl 0
  | cons q qs ih =>
      unfold listRemovePrime
      by_cases same : p = q
      · rw [if_pos same]
        exact Nat.le_trans ih (Nat.le_succ _)
      · rw [if_neg same]
        exact Nat.succ_le_succ ih

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

private theorem listContainsPrime_append_false {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = false -> listContainsPrime p ys = false ->
        listContainsPrime p (xs ++ ys) = false := by
  intro xs
  induction xs with
  | nil =>
      intro ys _absentLeft absentRight
      exact absentRight
  | cons q qs ih =>
      intro ys absentLeft absentRight
      change (if p = q then true else listContainsPrime p qs) = false at absentLeft
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = false
      by_cases same : p = q
      · rw [if_pos same] at absentLeft
        cases absentLeft
      · rw [if_neg same] at absentLeft
        rw [if_neg same]
        exact ih ys absentLeft absentRight

private theorem listContainsPrime_cons_self (p : BHist) (xs : List BHist) :
    listContainsPrime p (p :: xs) = true := by
  change (if p = p then true else listContainsPrime p xs) = true
  rw [if_pos rfl]

private theorem listContainsPrime_cons_true_of_tail {p q : BHist} {xs : List BHist} :
    listContainsPrime p xs = true -> listContainsPrime p (q :: xs) = true := by
  intro found
  change (if p = q then true else listContainsPrime p xs) = true
  by_cases same : p = q
  · rw [if_pos same]
  · rw [if_neg same]
    exact found

private theorem listMem_map_forward_pure {α β : Type} {f : α -> β} :
    ∀ {xs : List α} {y : β},
      y ∈ xs.map f -> ∃ x : α, x ∈ xs ∧ f x = y := by
  intro xs
  induction xs with
  | nil =>
      intro y member
      cases member
  | cons x rest ih =>
      intro y member
      change y ∈ f x :: rest.map f at member
      cases member with
      | head =>
          exact ⟨x, List.Mem.head rest, rfl⟩
      | tail _ tailMember =>
          cases ih tailMember with
          | intro source data =>
              exact ⟨source, List.Mem.tail x data.left, data.right⟩

private theorem listMem_append_forward_pure {α : Type} :
    ∀ {xs ys : List α} {z : α},
      z ∈ xs ++ ys -> z ∈ xs ∨ z ∈ ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys z member
      exact Or.inr member
  | cons x rest ih =>
      intro ys z member
      change z ∈ x :: (rest ++ ys) at member
      cases member with
      | head =>
          exact Or.inl (List.Mem.head rest)
      | tail _ tailMember =>
          cases ih tailMember with
          | inl leftMember =>
              exact Or.inl (List.Mem.tail x leftMember)
          | inr rightMember =>
              exact Or.inr rightMember

private theorem mem_appendFactorListProducts
    {left right : List (List BHist)} {fs : List BHist} :
    fs ∈ appendFactorListProducts left right ->
      ∃ l : List BHist, ∃ r : List BHist,
        l ∈ left ∧ r ∈ right ∧ fs = l ++ r := by
  intro member
  induction right with
  | nil =>
      unfold appendFactorListProducts at member
      exact False.elim (List.not_mem_nil member)
  | cons r rs ih =>
      unfold appendFactorListProducts at member
      have split := listMem_append_forward_pure member
      cases split with
      | inl inHead =>
          have mapped := listMem_map_forward_pure inHead
          cases mapped with
          | intro l lData =>
              exact ⟨l, r, lData.left,
                (show r ∈ r :: rs from List.mem_cons_self), lData.right.symm⟩
      | inr inTail =>
          cases ih inTail with
          | intro l restData =>
              cases restData with
              | intro r' data =>
                  exact ⟨l, r', data.left,
                    List.mem_cons_of_mem r data.right.left, data.right.right⟩

private theorem list_map_map {α β γ : Type} (f : α -> β) (g : β -> γ) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x)) := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x rest ih =>
      change g (f x) :: (rest.map f).map g =
        g (f x) :: rest.map (fun y => g (f y))
      exact congrArg (fun tail => g (f x) :: tail) ih

private theorem primePowerFactorLists_absent_of_ne {p q : BHist} :
    ∀ n : Nat, (p = q -> False) ->
      ∀ fs : List BHist, fs ∈ primePowerFactorLists q n ->
        listContainsPrime p fs = false := by
  intro n
  induction n with
  | zero =>
      intro _ne fs member
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          exact False.elim (List.not_mem_nil tail)
  | succ n ih =>
      intro ne fs member
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          have mapped := listMem_map_forward_pure tail
          cases mapped with
          | intro gs gsData =>
              cases gsData.right
              change (if p = q then true else listContainsPrime p gs) = false
              by_cases same : p = q
              · exact False.elim (ne same)
              · rw [if_neg same]
                exact ih ne gs gsData.left

private theorem divisorFactorListsAux_seen_absent {p : BHist} :
    ∀ seen entries fs : List BHist,
      listContainsPrime p seen = true ->
        fs ∈ divisorFactorListsAux seen entries ->
          listContainsPrime p fs = false := by
  intro seen entries
  induction entries generalizing seen with
  | nil =>
      intro fs _seenHas member
      unfold divisorFactorListsAux at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          exact False.elim (List.not_mem_nil tail)
  | cons q qs ih =>
      intro fs seenHas member
      unfold divisorFactorListsAux at member
      by_cases qSeen : listContainsPrime q seen = true
      · rw [qSeen] at member
        exact ih seen fs seenHas member
      · have qSeenFalse : listContainsPrime q seen = false := by
          cases h : listContainsPrime q seen
          · rfl
          · exact False.elim (qSeen h)
        rw [qSeenFalse] at member
        cases mem_appendFactorListProducts member with
        | intro left leftData =>
            cases leftData with
            | intro right data =>
                cases data.right.right
                have pNeQ : p = q -> False := by
                  intro same
                  cases same
                  rw [seenHas] at qSeenFalse
                  cases qSeenFalse
                have leftAbsent :
                    listContainsPrime p left = false :=
                  primePowerFactorLists_absent_of_ne
                    (listPrimeCountNat q qs + 1) pNeQ left data.left
                have seenTail : listContainsPrime p (q :: seen) = true :=
                  listContainsPrime_cons_true_of_tail seenHas
                have rightAbsent :
                    listContainsPrime p right = false :=
                  ih (q :: seen) right seenTail data.right.left
                exact listContainsPrime_append_false left right leftAbsent rightAbsent

private theorem mobiusFactorListSum_all_zero :
    ∀ factorLists : List (List BHist),
      (∀ fs : List BHist, fs ∈ factorLists ->
        IntEq (mobiusFactorsIntegerUp fs) intZero) ->
        IntEq (mobiusFactorListSum factorLists) intZero := by
  intro factorLists
  induction factorLists with
  | nil =>
      intro _allZero
      exact IntEq_refl intZero
  | cons fs fss ih =>
      intro allZero
      change IntEq
        (IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum fss))
        intZero
      have headZero : IntEq (mobiusFactorsIntegerUp fs) intZero :=
        allZero fs (show fs ∈ fs :: fss from List.mem_cons_self)
      have tailZero : IntEq (mobiusFactorListSum fss) intZero :=
        ih (fun gs mem => allZero gs (List.mem_cons_of_mem fs mem))
      have addZero :
          IntEq
            (IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum fss))
            (IntAdd intZero intZero) :=
        BEDC.Derived.RationalUp.IntAdd_respects headZero tailZero
      exact IntEq_trans addZero (IntAdd_zero_left intZero)

private theorem mobiusFactorListSum_append (xs ys : List (List BHist)) :
    IntEq (mobiusFactorListSum (xs ++ ys))
      (IntAdd (mobiusFactorListSum xs) (mobiusFactorListSum ys)) := by
  induction xs with
  | nil =>
      change IntEq (mobiusFactorListSum ys)
        (IntAdd intZero (mobiusFactorListSum ys))
      exact IntEq_symm (IntAdd_zero_left (mobiusFactorListSum ys))
  | cons fs fss ih =>
      change IntEq
        (IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum (fss ++ ys)))
        (IntAdd
          (IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum fss))
          (mobiusFactorListSum ys))
      have inner :
          IntEq
            (IntAdd (mobiusFactorsIntegerUp fs) (mobiusFactorListSum (fss ++ ys)))
            (IntAdd (mobiusFactorsIntegerUp fs)
              (IntAdd (mobiusFactorListSum fss) (mobiusFactorListSum ys))) :=
        BEDC.Derived.RationalUp.IntAdd_respects
          (IntEq_refl (mobiusFactorsIntegerUp fs)) ih
      exact IntEq_trans inner
        (IntEq_symm (BEDC.Derived.RationalUp.IntAdd_assoc (mobiusFactorsIntegerUp fs)
          (mobiusFactorListSum fss) (mobiusFactorListSum ys)))

private theorem mobiusDoublePrimePowerAppend_all_zero
    (p : BHist) (rest : List BHist) (n : Nat) :
    IntEq
      (mobiusFactorListSum
        ((primePowerFactorLists p n).map (fun fs => p :: p :: (fs ++ rest))))
      intZero := by
  apply mobiusFactorListSum_all_zero
  intro fs member
  have mapped := listMem_map_forward_pure member
  cases mapped with
  | intro base data =>
      cases data.right
      exact mobiusFactorsIntegerUp_repeated_zero
        (listContainsPrime_cons_self p (base ++ rest))

private theorem mobiusSinglePrimePowerAppend_sum_neg
    (p : BHist) (rest : List BHist) :
    ∀ n : Nat, listContainsPrime p rest = false ->
      IntEq
        (mobiusFactorListSum
          ((primePowerFactorLists p n).map (fun fs => p :: fs ++ rest)))
        (IntNeg (mobiusFactorsIntegerUp rest)) := by
  intro n absent
  cases n with
  | zero =>
      change IntEq
        (IntAdd (mobiusFactorsIntegerUp (p :: rest)) intZero)
        (IntNeg (mobiusFactorsIntegerUp rest))
      have head :
          IntEq (mobiusFactorsIntegerUp (p :: rest))
            (IntNeg (mobiusFactorsIntegerUp rest)) := by
        change IntEq
          (if listContainsPrime p rest then intZero
            else IntNeg (mobiusFactorsIntegerUp rest))
          (IntNeg (mobiusFactorsIntegerUp rest))
        rw [absent]
        exact IntEq_refl (IntNeg (mobiusFactorsIntegerUp rest))
      exact IntEq_trans
        (BEDC.Derived.RationalUp.IntAdd_zero (mobiusFactorsIntegerUp (p :: rest)))
        head
  | succ n =>
      unfold primePowerFactorLists
      change IntEq
        (IntAdd (mobiusFactorsIntegerUp (p :: rest))
          (mobiusFactorListSum
            (((primePowerFactorLists p n).map (fun fs => p :: fs)).map
              (fun fs => p :: fs ++ rest))))
        (IntNeg (mobiusFactorsIntegerUp rest))
      rw [list_map_map (fun fs : List BHist => p :: fs)
        (fun fs : List BHist => p :: fs ++ rest)]
      change IntEq
        (IntAdd (mobiusFactorsIntegerUp (p :: rest))
          (mobiusFactorListSum
            ((primePowerFactorLists p n).map
              (fun fs => p :: p :: (fs ++ rest)))))
        (IntNeg (mobiusFactorsIntegerUp rest))
      have head :
          IntEq (mobiusFactorsIntegerUp (p :: rest))
            (IntNeg (mobiusFactorsIntegerUp rest)) := by
        change IntEq
          (if listContainsPrime p rest then intZero
            else IntNeg (mobiusFactorsIntegerUp rest))
          (IntNeg (mobiusFactorsIntegerUp rest))
        rw [absent]
        exact IntEq_refl (IntNeg (mobiusFactorsIntegerUp rest))
      have tail :
          IntEq
            (mobiusFactorListSum
              ((primePowerFactorLists p n).map
                (fun fs => p :: p :: (fs ++ rest))))
            intZero :=
        mobiusDoublePrimePowerAppend_all_zero p rest n
      have combined :
          IntEq
            (IntAdd (mobiusFactorsIntegerUp (p :: rest))
              (mobiusFactorListSum
                ((primePowerFactorLists p n).map
                  (fun fs => p :: p :: (fs ++ rest)))))
            (IntAdd (IntNeg (mobiusFactorsIntegerUp rest)) intZero) :=
        BEDC.Derived.RationalUp.IntAdd_respects head tail
      exact IntEq_trans combined
        (BEDC.Derived.RationalUp.IntAdd_zero (IntNeg (mobiusFactorsIntegerUp rest)))

private theorem mobiusPrimePowerAppendBlock_zero
    (p : BHist) (rest : List BHist) (n : Nat) :
    listContainsPrime p rest = false ->
      IntEq
        (mobiusFactorListSum
          ((primePowerFactorLists p (n + 1)).map (fun fs => fs ++ rest)))
        intZero := by
  intro absent
  unfold primePowerFactorLists
  change IntEq
    (IntAdd (mobiusFactorsIntegerUp rest)
      (mobiusFactorListSum
        (((primePowerFactorLists p n).map (fun fs => p :: fs)).map
          (fun fs => fs ++ rest))))
    intZero
  rw [list_map_map (fun fs : List BHist => p :: fs)
    (fun fs : List BHist => fs ++ rest)]
  change IntEq
    (IntAdd (mobiusFactorsIntegerUp rest)
      (mobiusFactorListSum
        ((primePowerFactorLists p n).map (fun fs => p :: fs ++ rest))))
    intZero
  have tail :
      IntEq
        (mobiusFactorListSum
          ((primePowerFactorLists p n).map (fun fs => p :: fs ++ rest)))
        (IntNeg (mobiusFactorsIntegerUp rest)) :=
    mobiusSinglePrimePowerAppend_sum_neg p rest n absent
  have combined :
      IntEq
        (IntAdd (mobiusFactorsIntegerUp rest)
          (mobiusFactorListSum
            ((primePowerFactorLists p n).map (fun fs => p :: fs ++ rest))))
        (IntAdd (mobiusFactorsIntegerUp rest)
          (IntNeg (mobiusFactorsIntegerUp rest))) :=
    BEDC.Derived.RationalUp.IntAdd_respects
      (IntEq_refl (mobiusFactorsIntegerUp rest)) tail
  exact IntEq_trans combined
    (BEDC.Derived.RationalUp.IntAdd_neg (mobiusFactorsIntegerUp rest))

private theorem mobiusFactorListSum_appendFactorListProducts_zero
    (left right : List (List BHist)) :
    (∀ rest : List BHist, rest ∈ right ->
      IntEq (mobiusFactorListSum (left.map (fun l => l ++ rest))) intZero) ->
      IntEq (mobiusFactorListSum (appendFactorListProducts left right)) intZero := by
  intro blockZero
  induction right with
  | nil =>
      exact IntEq_refl intZero
  | cons rest rests ih =>
      unfold appendFactorListProducts
      have split :
          IntEq
            (mobiusFactorListSum
              ((left.map (fun l => l ++ rest)) ++
                appendFactorListProducts left rests))
            (IntAdd
              (mobiusFactorListSum (left.map (fun l => l ++ rest)))
              (mobiusFactorListSum (appendFactorListProducts left rests))) :=
        mobiusFactorListSum_append (left.map (fun l => l ++ rest))
          (appendFactorListProducts left rests)
      have headZero :
          IntEq (mobiusFactorListSum (left.map (fun l => l ++ rest))) intZero :=
        blockZero rest (show rest ∈ rest :: rests from List.mem_cons_self)
      have tailZero :
          IntEq (mobiusFactorListSum (appendFactorListProducts left rests)) intZero :=
        ih (fun r mem => blockZero r (List.mem_cons_of_mem rest mem))
      have bothZero :
          IntEq
            (IntAdd
              (mobiusFactorListSum (left.map (fun l => l ++ rest)))
              (mobiusFactorListSum (appendFactorListProducts left rests)))
            (IntAdd intZero intZero) :=
        BEDC.Derived.RationalUp.IntAdd_respects headZero tailZero
      exact IntEq_trans split (IntEq_trans bothZero (IntAdd_zero_left intZero))

private theorem mobiusPrimePowerProducts_zero
    (p : BHist) (right : List (List BHist)) (n : Nat) :
    (∀ rest : List BHist, rest ∈ right ->
      listContainsPrime p rest = false) ->
      IntEq
        (mobiusFactorListSum
          (appendFactorListProducts (primePowerFactorLists p (n + 1)) right))
        intZero := by
  intro rightAbsent
  exact mobiusFactorListSum_appendFactorListProducts_zero
    (primePowerFactorLists p (n + 1)) right
    (fun rest mem => mobiusPrimePowerAppendBlock_zero p rest n
      (rightAbsent rest mem))

theorem sum_mobius_eq_indicator (entries : List BHist) :
    IntEq (mobiusDivisorSumFactors entries) (mobiusIndicatorIntegerUp entries) := by
  cases entries with
  | nil =>
      change IntEq (IntAdd intOne intZero) intOne
      exact BEDC.Derived.RationalUp.IntAdd_zero intOne
  | cons p ps =>
      change IntEq
        (mobiusFactorListSum
          (appendFactorListProducts
            (primePowerFactorLists p (listPrimeCountNat p ps + 1))
            (divisorFactorListsAux [p] ps)))
        intZero
      exact mobiusPrimePowerProducts_zero p (divisorFactorListsAux [p] ps)
        (listPrimeCountNat p ps)
        (fun rest mem =>
          divisorFactorListsAux_seen_absent [p] ps rest
            (listContainsPrime_cons_self p []) mem)

theorem eulerPhiFactorsNat_append_disjoint
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      eulerPhiFactorsNat (xs ++ ys) =
        eulerPhiFactorsNat xs * eulerPhiFactorsNat ys := by
  intro common
  induction xs with
  | nil =>
      change eulerPhiFactorsNat ys = 1 * eulerPhiFactorsNat ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      unfold listNoCommonPrime at common
      change
        (if listContainsPrime p (ps ++ ys)
          then bwordLength p * eulerPhiFactorsNat (ps ++ ys)
          else (bwordLength p - 1) * eulerPhiFactorsNat (ps ++ ys)) =
            (if listContainsPrime p ps
              then bwordLength p * eulerPhiFactorsNat ps
              else (bwordLength p - 1) * eulerPhiFactorsNat ps) *
                eulerPhiFactorsNat ys
      cases memPs : listContainsPrime p ps
      · have notAppend : listContainsPrime p (ps ++ ys) = false :=
          listContainsPrime_append_false ps ys memPs common.left
        rw [notAppend]
        change
          (bwordLength p - 1) * eulerPhiFactorsNat (ps ++ ys) =
            ((bwordLength p - 1) * eulerPhiFactorsNat ps) *
              eulerPhiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p - 1)
          (eulerPhiFactorsNat ps) (eulerPhiFactorsNat ys)).symm
      · have memAppend : listContainsPrime p (ps ++ ys) = true :=
          listContainsPrime_append_true_left ps ys memPs
        rw [memAppend]
        change
          bwordLength p * eulerPhiFactorsNat (ps ++ ys) =
            (bwordLength p * eulerPhiFactorsNat ps) *
              eulerPhiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p)
          (eulerPhiFactorsNat ps) (eulerPhiFactorsNat ys)).symm

theorem eulerPhiFactors_append_disjoint_hsame
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      hsame (eulerPhiFactors (xs ++ ys))
        (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro common
  unfold eulerPhiFactors
  exact congrArg natToUnary (eulerPhiFactorsNat_append_disjoint xs ys common)

theorem PrimeFactorizationProduct_append_mul
    {xs ys : List BHist} {m n mn : BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          PrimeFactorizationProduct (xs ++ ys) mn := by
  intro fx fy mul
  induction xs generalizing m mn with
  | nil =>
      have mUnit : hsame m NatOne := fx
      have shifted : NatMul NatOne n mn :=
        (NatMul_multiplicand_hsame_transport mUnit mul).right
      have sameNMn : hsame n mn :=
        hsame_symm (NatMul_unit_left_hsame
          (PrimeFactorizationProduct_result_unary fy) shifted)
      exact PrimeFactorizationProduct_result_hsame_transport fy sameNMn
  | cons p ps ih =>
      cases fx with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              have tailUnary : UnaryHistory tailProduct :=
                PrimeFactorizationProduct_result_unary tailData.left
              have nUnary : UnaryHistory n :=
                PrimeFactorizationProduct_result_unary fy
              cases NatMul_total tailUnary nUnary with
              | intro tailN tailNData =>
                  have tailProductFactor :
                      PrimeFactorizationProduct (ps ++ ys) tailN :=
                    ih tailData.left tailNData.right
                  have tailNUnary : UnaryHistory tailN := tailNData.left
                  cases NatMul_total pPrime.left tailNUnary with
                  | intro displayed displayedData =>
                      have sameMnDisplayed : hsame mn displayed :=
                        NatMul_assoc_hsame pPrime.left tailUnary nUnary
                          tailData.right mul tailNData.right displayedData.right
                      have pTailNAtMn : NatMul p tailN mn :=
                        (NatMul_result_hsame_transport displayedData.right
                          (hsame_symm sameMnDisplayed)).right
                      exact ⟨pPrime, tailN, tailProductFactor, pTailNAtMn⟩

theorem listContainsPrime_product_divides
    {p : BHist} {xs : List BHist} {n : BHist} :
    listContainsPrime p xs = true ->
      PrimeFactorizationProduct xs n ->
        NatDivides p n := by
  intro found product
  induction xs generalizing n with
  | nil =>
      cases found
  | cons q qs ih =>
      change (if p = q then true else listContainsPrime p qs) = true at found
      cases product with
      | intro qPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              by_cases same : p = q
              · rw [if_pos same] at found
                have qDividesN : NatDivides q n :=
                  ⟨tailProduct, PrimeFactorizationProduct_result_unary tailData.left,
                    tailData.right⟩
                exact (NatDivides_divisor_hsame_transport qDividesN (hsame_symm same)).right
              · rw [if_neg same] at found
                have pDividesTail : NatDivides p tailProduct :=
                  ih found tailData.left
                cases NatMul_total
                    (PrimeFactorizationProduct_result_unary tailData.left) qPrime.left with
                | intro displayed displayedData =>
                    have sameDisplayedN : hsame displayed n :=
                      NatMul_comm_hsame
                        (PrimeFactorizationProduct_result_unary tailData.left)
                        qPrime.left displayedData.right tailData.right
                    have tailQProduct : NatMul tailProduct q n :=
                      (NatMul_result_hsame_transport displayedData.right sameDisplayedN).right
                    exact NatDivides_mul_right_factor_closed qPrime.left
                      pDividesTail tailQProduct

private theorem listContainsPrime_false_of_not_divides
    {p : BHist} {xs : List BHist} {n : BHist} :
    PrimeFactorizationProduct xs n ->
      (NatDivides p n -> False) ->
        listContainsPrime p xs = false := by
  intro product notDivides
  cases found : listContainsPrime p xs
  · rfl
  · exact False.elim (notDivides (listContainsPrime_product_divides found product))

theorem PrimeFactorizationProduct_coprime_no_common
    {m n : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatGcd m n NatOne ->
          listNoCommonPrime xs ys := by
  intro fx fy gcd
  induction xs generalizing m with
  | nil =>
      trivial
  | cons p ps ih =>
      cases fx with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold listNoCommonPrime
              constructor
              · have pDividesM : NatDivides p m :=
                  ⟨tailProduct, PrimeFactorizationProduct_result_unary tailData.left,
                    tailData.right⟩
                have notDividesN : NatDivides p n -> False := by
                  intro pDividesN
                  have pDividesUnit : NatDivides p NatOne :=
                    NatGcd_greatest gcd pDividesM pDividesN
                  have pUnit : hsame p NatOne :=
                    (NatDivides_unit_right_iff.mp pDividesUnit)
                  cases pUnit
                  exact NatPrime_unit_absurd pPrime
                exact listContainsPrime_false_of_not_divides fy notDividesN
              · have tailDividesM : NatDivides tailProduct m :=
                  NatDivides_mul_right_closed pPrime.left
                    (PrimeFactorizationProduct_result_unary tailData.left)
                    tailData.right
                have tailGcd : NatGcd tailProduct n NatOne := by
                  constructor
                  · exact PrimeFactorizationProduct_result_unary tailData.left
                  · constructor
                    · exact NatGcd_right_unary gcd
                    · constructor
                      · exact NatGcd_result_unary gcd
                      · constructor
                        · exact (NatDivides_reflexive_pair
                            (PrimeFactorizationProduct_result_unary tailData.left)).left
                        · constructor
                          · exact NatGcd_dvd_right gcd
                          · intro d dividesTail dividesN
                            exact NatGcd_greatest gcd
                              (NatDivides_transitive dividesTail tailDividesM) dividesN
                exact ih tailData.left tailGcd

theorem eulerPhi_factorization_product_multiplicative
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          listNoCommonPrime xs ys ->
            EulerPhiOfFactorization mn
              (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro fx fy mul common
  have product : PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx fy mul
  exact ⟨xs ++ ys,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    hsame_symm (eulerPhiFactors_append_disjoint_hsame xs ys common)⟩

theorem eulerPhi_factorization_product_multiplicative_of_gcd_one
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            EulerPhiOfFactorization mn
              (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro fx fy mul gcd
  exact eulerPhi_factorization_product_multiplicative fx fy mul
    (PrimeFactorizationProduct_coprime_no_common fx fy gcd)

end BEDC.Derived.ArithmeticFnUp

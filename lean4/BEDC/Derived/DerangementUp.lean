import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.FactorialUp

namespace BEDC.Derived.DerangementUp

abbrev factorialCount (n : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount n

abbrev binomialCount (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def derangementNumber : Nat -> Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementNumber (n + 1) + derangementNumber n)

def alternatingPositive : Nat -> Bool
  | 0 => true
  | Nat.succ n =>
      match alternatingPositive n with
      | true => false
      | false => true

def signedStepBalance : Nat -> Prop
  | 0 => derangementNumber 0 = 1
  | Nat.succ n =>
      match alternatingPositive (Nat.succ n) with
      | true =>
          derangementNumber (Nat.succ n) =
            Nat.succ n * derangementNumber n + 1
      | false =>
          derangementNumber (Nat.succ n) + 1 =
            Nat.succ n * derangementNumber n

private theorem nat_signed_step_from_negative (m a b : Nat) :
    a + 1 = m * b ->
      m * (a + b) = Nat.succ m * a + 1 := by
  intro h
  calc
    m * (a + b) = m * a + m * b := Nat.mul_add m a b
    _ = m * a + (a + 1) := congrArg (fun t => m * a + t) h.symm
    _ = m * a + a + 1 := (Nat.add_assoc (m * a) a 1).symm
    _ = Nat.succ m * a + 1 := by
      rw [Nat.succ_mul]

private theorem nat_signed_step_from_positive (m a b : Nat) :
    a = m * b + 1 ->
      m * (a + b) + 1 = Nat.succ m * a := by
  intro h
  calc
    m * (a + b) + 1 = (m * a + m * b) + 1 := by
      rw [Nat.mul_add]
    _ = m * a + (m * b + 1) := Nat.add_assoc (m * a) (m * b) 1
    _ = m * a + a := congrArg (fun t => m * a + t) h.symm
    _ = Nat.succ m * a := by
      rw [Nat.succ_mul]

theorem derangementNumber_signed_recurrence_balance (n : Nat) :
    signedStepBalance n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      induction n with
      | zero =>
          rfl
      | succ n ih =>
          change
            match alternatingPositive (Nat.succ n) with
            | true =>
                derangementNumber (Nat.succ n) =
                  Nat.succ n * derangementNumber n + 1
            | false =>
                derangementNumber (Nat.succ n) + 1 =
                  Nat.succ n * derangementNumber n at ih
          change
            match alternatingPositive (Nat.succ (Nat.succ n)) with
            | true =>
                derangementNumber (Nat.succ (Nat.succ n)) =
                  Nat.succ (Nat.succ n) * derangementNumber (Nat.succ n) + 1
            | false =>
                derangementNumber (Nat.succ (Nat.succ n)) + 1 =
                  Nat.succ (Nat.succ n) * derangementNumber (Nat.succ n)
          unfold alternatingPositive
          cases h : alternatingPositive (Nat.succ n)
          · rw [h] at ih
            change
              derangementNumber (Nat.succ n) + 1 =
                Nat.succ n * derangementNumber n at ih
            change (Nat.succ n) *
                (derangementNumber (Nat.succ n) + derangementNumber n) =
              Nat.succ (Nat.succ n) * derangementNumber (Nat.succ n) + 1
            exact nat_signed_step_from_negative (Nat.succ n)
              (derangementNumber (Nat.succ n)) (derangementNumber n) ih
          · rw [h] at ih
            change
              derangementNumber (Nat.succ n) =
                Nat.succ n * derangementNumber n + 1 at ih
            change (Nat.succ n) *
                (derangementNumber (Nat.succ n) + derangementNumber n) + 1 =
              Nat.succ (Nat.succ n) * derangementNumber (Nat.succ n)
            exact nat_signed_step_from_positive (Nat.succ n)
              (derangementNumber (Nat.succ n)) (derangementNumber n) ih

def factorialQuotientLayerRow : Nat -> List Nat
  | 0 => [1]
  | Nat.succ n =>
      List.map (fun value => Nat.succ n * value) (factorialQuotientLayerRow n) ++ [1]

def signedFactorialLayerRow : Nat -> List (Bool × Nat)
  | 0 => [(true, 1)]
  | Nat.succ n =>
      List.map (fun layer => (layer.fst, Nat.succ n * layer.snd))
        (signedFactorialLayerRow n) ++ [(alternatingPositive (Nat.succ n), 1)]

def natListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListSum xs

def signedLayerPositiveValue : Bool × Nat -> Nat
  | (true, value) => value
  | (false, _value) => 0

def signedLayerNegativeValue : Bool × Nat -> Nat
  | (true, _value) => 0
  | (false, value) => value

def factorialClosedPositive : Nat -> Nat
  | 0 => 1
  | Nat.succ n =>
      match alternatingPositive (Nat.succ n) with
      | true => Nat.succ n * factorialClosedPositive n + 1
      | false => Nat.succ n * factorialClosedPositive n

def factorialClosedNegative : Nat -> Nat
  | 0 => 0
  | Nat.succ n =>
      match alternatingPositive (Nat.succ n) with
      | true => Nat.succ n * factorialClosedNegative n
      | false => Nat.succ n * factorialClosedNegative n + 1

def factorialClosedPositiveList (n : Nat) : Nat :=
  natListSum (List.map signedLayerPositiveValue (signedFactorialLayerRow n))

def factorialClosedNegativeList (n : Nat) : Nat :=
  natListSum (List.map signedLayerNegativeValue (signedFactorialLayerRow n))

private theorem natListSum_append :
    ∀ xs ys : List Nat, natListSum (xs ++ ys) = natListSum xs + natListSum ys
  | [], ys => by
      change natListSum ys = 0 + natListSum ys
      exact (Nat.zero_add (natListSum ys)).symm
  | x :: xs, ys => by
      change x + natListSum (xs ++ ys) = x + natListSum xs + natListSum ys
      rw [natListSum_append xs ys]
      exact (Nat.add_assoc x (natListSum xs) (natListSum ys)).symm

private theorem natListSum_map_mul (m : Nat) :
    ∀ xs : List Nat,
      natListSum (List.map (fun value => m * value) xs) = m * natListSum xs
  | [] => by
      exact (Nat.mul_zero m).symm
  | x :: xs => by
      change m * x + natListSum (List.map (fun value => m * value) xs) =
        m * (x + natListSum xs)
      rw [natListSum_map_mul m xs]
      exact (Nat.mul_add m x (natListSum xs)).symm

private theorem positiveValue_scaled (m : Nat) (layer : Bool × Nat) :
    signedLayerPositiveValue (layer.fst, m * layer.snd) =
      m * signedLayerPositiveValue layer := by
  cases layer with
  | mk sign value =>
      cases sign <;> rfl

private theorem negativeValue_scaled (m : Nat) (layer : Bool × Nat) :
    signedLayerNegativeValue (layer.fst, m * layer.snd) =
      m * signedLayerNegativeValue layer := by
  cases layer with
  | mk sign value =>
      cases sign <;> rfl

private theorem map_positive_scaled (m : Nat) :
    ∀ xs : List (Bool × Nat),
      List.map signedLayerPositiveValue
          (List.map (fun layer => (layer.fst, m * layer.snd)) xs) =
        List.map (fun value => m * value)
          (List.map signedLayerPositiveValue xs)
  | [] => rfl
  | x :: xs => by
      change signedLayerPositiveValue (x.fst, m * x.snd) ::
          List.map signedLayerPositiveValue
            (List.map (fun layer => (layer.fst, m * layer.snd)) xs) =
        m * signedLayerPositiveValue x ::
          List.map (fun value => m * value)
            (List.map signedLayerPositiveValue xs)
      rw [positiveValue_scaled m x]
      rw [map_positive_scaled m xs]

private theorem map_negative_scaled (m : Nat) :
    ∀ xs : List (Bool × Nat),
      List.map signedLayerNegativeValue
          (List.map (fun layer => (layer.fst, m * layer.snd)) xs) =
        List.map (fun value => m * value)
          (List.map signedLayerNegativeValue xs)
  | [] => rfl
  | x :: xs => by
      change signedLayerNegativeValue (x.fst, m * x.snd) ::
          List.map signedLayerNegativeValue
            (List.map (fun layer => (layer.fst, m * layer.snd)) xs) =
        m * signedLayerNegativeValue x ::
          List.map (fun value => m * value)
            (List.map signedLayerNegativeValue xs)
      rw [negativeValue_scaled m x]
      rw [map_negative_scaled m xs]

private theorem map_positive_append :
    ∀ xs ys : List (Bool × Nat),
      List.map signedLayerPositiveValue (xs ++ ys) =
        List.map signedLayerPositiveValue xs ++
          List.map signedLayerPositiveValue ys
  | [], _ys => rfl
  | x :: xs, ys => by
      change signedLayerPositiveValue x ::
          List.map signedLayerPositiveValue (xs ++ ys) =
        signedLayerPositiveValue x ::
          (List.map signedLayerPositiveValue xs ++
            List.map signedLayerPositiveValue ys)
      rw [map_positive_append xs ys]

private theorem map_negative_append :
    ∀ xs ys : List (Bool × Nat),
      List.map signedLayerNegativeValue (xs ++ ys) =
        List.map signedLayerNegativeValue xs ++
          List.map signedLayerNegativeValue ys
  | [], _ys => rfl
  | x :: xs, ys => by
      change signedLayerNegativeValue x ::
          List.map signedLayerNegativeValue (xs ++ ys) =
        signedLayerNegativeValue x ::
          (List.map signedLayerNegativeValue xs ++
            List.map signedLayerNegativeValue ys)
      rw [map_negative_append xs ys]

theorem factorialClosedPositive_list (n : Nat) :
    factorialClosedPositiveList n = factorialClosedPositive n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold factorialClosedPositiveList signedFactorialLayerRow
      rw [map_positive_append]
      rw [natListSum_append]
      rw [map_positive_scaled (Nat.succ n) (signedFactorialLayerRow n)]
      rw [natListSum_map_mul]
      unfold factorialClosedPositiveList at ih
      rw [ih]
      rw [Nat.add_one]
      change Nat.succ n * factorialClosedPositive n +
          natListSum (List.map signedLayerPositiveValue
            [(alternatingPositive (Nat.succ n), 1)]) =
        match alternatingPositive (Nat.succ n) with
        | true => Nat.succ n * factorialClosedPositive n + 1
        | false => Nat.succ n * factorialClosedPositive n
      cases h : alternatingPositive (Nat.succ n)
      · change Nat.succ n * factorialClosedPositive n + 0 =
          Nat.succ n * factorialClosedPositive n
        exact Nat.add_zero (Nat.succ n * factorialClosedPositive n)
      · change Nat.succ n * factorialClosedPositive n + 1 =
          Nat.succ n * factorialClosedPositive n + 1
        rfl

theorem factorialClosedNegative_list (n : Nat) :
    factorialClosedNegativeList n = factorialClosedNegative n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold factorialClosedNegativeList signedFactorialLayerRow
      rw [map_negative_append]
      rw [natListSum_append]
      rw [map_negative_scaled (Nat.succ n) (signedFactorialLayerRow n)]
      rw [natListSum_map_mul]
      unfold factorialClosedNegativeList at ih
      rw [ih]
      rw [Nat.add_one]
      change Nat.succ n * factorialClosedNegative n +
          natListSum (List.map signedLayerNegativeValue
            [(alternatingPositive (Nat.succ n), 1)]) =
        match alternatingPositive (Nat.succ n) with
        | true => Nat.succ n * factorialClosedNegative n
        | false => Nat.succ n * factorialClosedNegative n + 1
      cases h : alternatingPositive (Nat.succ n)
      · change Nat.succ n * factorialClosedNegative n + 1 =
          Nat.succ n * factorialClosedNegative n + 1
        rfl
      · change Nat.succ n * factorialClosedNegative n + 0 =
          Nat.succ n * factorialClosedNegative n
        exact Nat.add_zero (Nat.succ n * factorialClosedNegative n)

private theorem nat_closed_step_positive (m previous next pos neg : Nat) :
    previous + neg = pos ->
      next = m * previous + 1 ->
        next + (m * neg) = m * pos + 1 := by
  intro balance step
  calc
    next + (m * neg) = (m * previous + 1) + m * neg :=
      congrArg (fun t => t + m * neg) step
    _ = m * previous + (1 + m * neg) := Nat.add_assoc (m * previous) 1 (m * neg)
    _ = m * previous + (m * neg + 1) := by
      rw [Nat.add_comm 1 (m * neg)]
    _ = m * previous + m * neg + 1 :=
      (Nat.add_assoc (m * previous) (m * neg) 1).symm
    _ = m * (previous + neg) + 1 := by
      rw [Nat.mul_add]
    _ = m * pos + 1 := congrArg (fun t => m * t + 1) balance

private theorem nat_closed_step_negative (m previous next pos neg : Nat) :
    previous + neg = pos ->
      next + 1 = m * previous ->
        next + (m * neg + 1) = m * pos := by
  intro balance step
  calc
    next + (m * neg + 1) = next + (1 + m * neg) := by
      rw [Nat.add_comm (m * neg) 1]
    _ = next + 1 + m * neg := (Nat.add_assoc next 1 (m * neg)).symm
    _ = m * previous + m * neg := congrArg (fun t => t + m * neg) step
    _ = m * (previous + neg) := (Nat.mul_add m previous neg).symm
    _ = m * pos := congrArg (fun t => m * t) balance

theorem derangementNumber_factorial_closed_balance (n : Nat) :
    derangementNumber n + factorialClosedNegative n = factorialClosedPositive n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have step := derangementNumber_signed_recurrence_balance (Nat.succ n)
      change
        match alternatingPositive (Nat.succ n) with
        | true =>
            derangementNumber (Nat.succ n) =
              Nat.succ n * derangementNumber n + 1
        | false =>
            derangementNumber (Nat.succ n) + 1 =
              Nat.succ n * derangementNumber n at step
      rw [Nat.add_one]
      change
        derangementNumber (Nat.succ n) +
            (match alternatingPositive (Nat.succ n) with
            | true => Nat.succ n * factorialClosedNegative n
            | false => Nat.succ n * factorialClosedNegative n + 1) =
          match alternatingPositive (Nat.succ n) with
          | true => Nat.succ n * factorialClosedPositive n + 1
          | false => Nat.succ n * factorialClosedPositive n
      cases h : alternatingPositive (Nat.succ n) <;> rw [h] at step
      · change
          derangementNumber (Nat.succ n) +
              (Nat.succ n * factorialClosedNegative n + 1) =
            Nat.succ n * factorialClosedPositive n
        change
          derangementNumber (Nat.succ n) + 1 =
            Nat.succ n * derangementNumber n at step
        exact nat_closed_step_negative (Nat.succ n)
          (derangementNumber n) (derangementNumber (Nat.succ n))
          (factorialClosedPositive n)
          (factorialClosedNegative n) ih step
      · change
          derangementNumber (Nat.succ n) +
              Nat.succ n * factorialClosedNegative n =
            Nat.succ n * factorialClosedPositive n + 1
        change
          derangementNumber (Nat.succ n) =
            Nat.succ n * derangementNumber n + 1 at step
        exact nat_closed_step_positive (Nat.succ n)
          (derangementNumber n) (derangementNumber (Nat.succ n))
          (factorialClosedPositive n)
          (factorialClosedNegative n) ih step

def inclusionExclusionLayerCount (n k : Nat) : Nat :=
  binomialCount n k * factorialCount (n - k)

private theorem inclusionExclusionLayerCount_diagonal (n : Nat) :
    inclusionExclusionLayerCount n n = 1 := by
  unfold inclusionExclusionLayerCount binomialCount factorialCount
  rw [Nat.sub_self]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self n]
  rw [BEDC.Derived.PochhammerUp.natFactorialCount_zero]

def inclusionExclusionSignedLayerRow : Nat -> List (Bool × Nat)
  | 0 => [(true, inclusionExclusionLayerCount 0 0)]
  | Nat.succ n =>
      List.map (fun layer => (layer.fst, Nat.succ n * layer.snd))
        (inclusionExclusionSignedLayerRow n) ++
        [(alternatingPositive (Nat.succ n),
          inclusionExclusionLayerCount (Nat.succ n) (Nat.succ n))]

def inclusionExclusionPositive (n : Nat) : Nat :=
  natListSum (List.map signedLayerPositiveValue (inclusionExclusionSignedLayerRow n))

def inclusionExclusionNegative (n : Nat) : Nat :=
  natListSum (List.map signedLayerNegativeValue (inclusionExclusionSignedLayerRow n))

theorem inclusionExclusionSignedLayerRow_factorial (n : Nat) :
    inclusionExclusionSignedLayerRow n = signedFactorialLayerRow n := by
  induction n with
  | zero =>
      unfold inclusionExclusionSignedLayerRow signedFactorialLayerRow
      rw [inclusionExclusionLayerCount_diagonal 0]
  | succ n ih =>
      unfold inclusionExclusionSignedLayerRow signedFactorialLayerRow
      rw [ih]
      rw [inclusionExclusionLayerCount_diagonal (Nat.succ n)]

theorem inclusionExclusionPositive_factorial (n : Nat) :
    inclusionExclusionPositive n = factorialClosedPositiveList n := by
  unfold inclusionExclusionPositive factorialClosedPositiveList
  rw [inclusionExclusionSignedLayerRow_factorial n]

theorem inclusionExclusionNegative_factorial (n : Nat) :
    inclusionExclusionNegative n = factorialClosedNegativeList n := by
  unfold inclusionExclusionNegative factorialClosedNegativeList
  rw [inclusionExclusionSignedLayerRow_factorial n]

theorem derangementNumber_two_step_recurrence (n : Nat) :
    derangementNumber (n + 2) =
      (n + 1) * (derangementNumber (n + 1) + derangementNumber n) := by
  rfl

theorem derangementNumber_succ_succ_recurrence (n : Nat) :
    derangementNumber (Nat.succ (Nat.succ n)) =
      Nat.succ n * (derangementNumber (Nat.succ n) + derangementNumber n) := by
  rfl

theorem derangementNumber_first_order_positive {n : Nat} :
    alternatingPositive (Nat.succ n) = true ->
      derangementNumber (Nat.succ n) =
        Nat.succ n * derangementNumber n + 1 := by
  intro h
  have step := derangementNumber_signed_recurrence_balance (Nat.succ n)
  change
    match alternatingPositive (Nat.succ n) with
    | true =>
        derangementNumber (Nat.succ n) =
          Nat.succ n * derangementNumber n + 1
    | false =>
        derangementNumber (Nat.succ n) + 1 =
          Nat.succ n * derangementNumber n at step
  rw [h] at step
  exact step

theorem derangementNumber_first_order_negative {n : Nat} :
    alternatingPositive (Nat.succ n) = false ->
      derangementNumber (Nat.succ n) + 1 =
        Nat.succ n * derangementNumber n := by
  intro h
  have step := derangementNumber_signed_recurrence_balance (Nat.succ n)
  change
    match alternatingPositive (Nat.succ n) with
    | true =>
        derangementNumber (Nat.succ n) =
          Nat.succ n * derangementNumber n + 1
    | false =>
        derangementNumber (Nat.succ n) + 1 =
          Nat.succ n * derangementNumber n at step
  rw [h] at step
  exact step

theorem derangementNumber_factorial_closed_form (n : Nat) :
    derangementNumber n + factorialClosedNegativeList n =
      factorialClosedPositiveList n := by
  rw [factorialClosedNegative_list n]
  rw [factorialClosedPositive_list n]
  exact derangementNumber_factorial_closed_balance n

theorem derangementNumber_inclusion_exclusion (n : Nat) :
    derangementNumber n + inclusionExclusionNegative n =
      inclusionExclusionPositive n := by
  rw [inclusionExclusionNegative_factorial n]
  rw [inclusionExclusionPositive_factorial n]
  exact derangementNumber_factorial_closed_form n

theorem derangementNumber_zero :
    derangementNumber 0 = 1 := by
  rfl

theorem derangementNumber_one :
    derangementNumber 1 = 0 := by
  rfl

theorem derangementNumber_two :
    derangementNumber 2 = 1 := by
  rfl

theorem derangementNumber_three :
    derangementNumber 3 = 2 := by
  rfl

theorem derangementNumber_four :
    derangementNumber 4 = 9 := by
  rfl

theorem DerangementUp_constructive_export :
    derangementNumber 0 = 1 ∧
      derangementNumber 1 = 0 ∧
      (∀ n : Nat,
        derangementNumber (n + 2) =
          (n + 1) * (derangementNumber (n + 1) + derangementNumber n)) ∧
      (∀ n : Nat, signedStepBalance n) ∧
      (∀ n : Nat,
        derangementNumber n + factorialClosedNegativeList n =
          factorialClosedPositiveList n) ∧
      (∀ n : Nat,
        derangementNumber n + inclusionExclusionNegative n =
          inclusionExclusionPositive n) := by
  constructor
  · exact derangementNumber_zero
  · constructor
    · exact derangementNumber_one
    · constructor
      · intro n
        exact derangementNumber_two_step_recurrence n
      · constructor
        · intro n
          exact derangementNumber_signed_recurrence_balance n
        · constructor
          · intro n
            exact derangementNumber_factorial_closed_form n
          · intro n
            exact derangementNumber_inclusion_exclusion n

end BEDC.Derived.DerangementUp

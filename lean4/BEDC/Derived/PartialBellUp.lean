import BEDC.Derived.BellNumberUp

namespace BEDC.Derived.PartialBellUp

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

-- 单项式用系数和块大小计数表表示；第一个槽记录大小为一的块数。
structure PartialBellTerm where
  coeff : Nat
  profile : List Nat

def natPow (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ n => x * natPow x n

def profileBlockCount : List Nat -> Nat
  | [] => 0
  | c :: cs => c + profileBlockCount cs

def incFirst : List Nat -> List Nat
  | [] => [1]
  | c :: cs => Nat.succ c :: cs

def prependTerms (c : Nat) : List PartialBellTerm -> List PartialBellTerm
  | [] => []
  | t :: ts => { coeff := t.coeff, profile := c :: t.profile } :: prependTerms c ts

-- 把一个既有块加大一格；系数乘以可选块的个数。
def growProfile (coeff : Nat) : List Nat -> List PartialBellTerm
  | [] => []
  | 0 :: cs => prependTerms 0 (growProfile coeff cs)
  | Nat.succ d :: cs =>
      { coeff := coeff * Nat.succ d, profile := d :: incFirst cs } ::
        prependTerms (Nat.succ d) (growProfile coeff cs)

def growTerm (t : PartialBellTerm) : List PartialBellTerm :=
  growProfile t.coeff t.profile

def singletonTerm (t : PartialBellTerm) : PartialBellTerm :=
  { coeff := t.coeff, profile := incFirst t.profile }

def singletonTerms : List PartialBellTerm -> List PartialBellTerm
  | [] => []
  | t :: ts => singletonTerm t :: singletonTerms ts

def growTerms : List PartialBellTerm -> List PartialBellTerm
  | [] => []
  | t :: ts => growTerm t ++ growTerms ts

def partialBellTerms : Nat -> Nat -> List PartialBellTerm
  | 0, 0 => [{ coeff := 1, profile := [] }]
  | 0, Nat.succ _ => []
  | Nat.succ _, 0 => []
  | Nat.succ n, Nat.succ k =>
      singletonTerms (partialBellTerms n k) ++ growTerms (partialBellTerms n (Nat.succ k))

def profileEval (weights : Nat -> Nat) : Nat -> List Nat -> Nat
  | _, [] => 1
  | start, c :: cs => natPow (weights start) c * profileEval weights (Nat.succ start) cs

def termEval (weights : Nat -> Nat) (t : PartialBellTerm) : Nat :=
  t.coeff * profileEval weights 1 t.profile

def termsEval (weights : Nat -> Nat) : List PartialBellTerm -> Nat
  | [] => 0
  | t :: ts => termEval weights t + termsEval weights ts

def partialBell (weights : Nat -> Nat) (n k : Nat) : Nat :=
  termsEval weights (partialBellTerms n k)

def completeBellPrefix (weights : Nat -> Nat) (n : Nat) : Nat -> Nat
  | 0 => partialBell weights n 0
  | Nat.succ k => completeBellPrefix weights n k + partialBell weights n (Nat.succ k)

def completeBell (weights : Nat -> Nat) (n : Nat) : Nat :=
  completeBellPrefix weights n n

def faaDiBrunoCoefficient (weights : Nat -> Nat) (n k : Nat) : Nat :=
  partialBell weights n k

inductive TermsHaveBlockCount (k : Nat) : List PartialBellTerm -> Prop where
  | nil : TermsHaveBlockCount k []
  | cons {t : PartialBellTerm} {ts : List PartialBellTerm} :
      profileBlockCount t.profile = k ->
        TermsHaveBlockCount k ts -> TermsHaveBlockCount k (t :: ts)

def coeffSum : List PartialBellTerm -> Nat
  | [] => 0
  | t :: ts => t.coeff + coeffSum ts

def weightedBlockSum : List PartialBellTerm -> Nat
  | [] => 0
  | t :: ts => t.coeff * profileBlockCount t.profile + weightedBlockSum ts

theorem natPow_one :
    forall k : Nat, natPow 1 k = 1
  | 0 => rfl
  | Nat.succ k => by
      change 1 * natPow 1 k = 1
      rw [natPow_one k]

theorem profileEval_allOnes (start : Nat) :
    forall p : List Nat, profileEval (fun _ => 1) start p = 1
  | [] => rfl
  | c :: cs => by
      change natPow 1 c * profileEval (fun _ => 1) (Nat.succ start) cs = 1
      rw [natPow_one c]
      rw [profileEval_allOnes (Nat.succ start) cs]

theorem termEval_allOnes (t : PartialBellTerm) :
    termEval (fun _ => 1) t = t.coeff := by
  unfold termEval
  rw [profileEval_allOnes 1 t.profile]
  exact Nat.mul_one t.coeff

theorem termsEval_allOnes :
    forall ts : List PartialBellTerm, termsEval (fun _ => 1) ts = coeffSum ts
  | [] => rfl
  | t :: ts => by
      change termEval (fun _ => 1) t + termsEval (fun _ => 1) ts =
        t.coeff + coeffSum ts
      rw [termEval_allOnes t]
      rw [termsEval_allOnes ts]

theorem termsEval_append (weights : Nat -> Nat) :
    forall xs ys : List PartialBellTerm,
      termsEval weights (xs ++ ys) = termsEval weights xs + termsEval weights ys
  | [], ys => (Nat.zero_add (termsEval weights ys)).symm
  | t :: ts, ys => by
      change termEval weights t + termsEval weights (ts ++ ys) =
        (termEval weights t + termsEval weights ts) + termsEval weights ys
      rw [termsEval_append weights ts ys]
      exact (Nat.add_assoc (termEval weights t) (termsEval weights ts)
        (termsEval weights ys)).symm

theorem coeffSum_append :
    forall xs ys : List PartialBellTerm,
      coeffSum (xs ++ ys) = coeffSum xs + coeffSum ys
  | [], ys => (Nat.zero_add (coeffSum ys)).symm
  | t :: ts, ys => by
      change t.coeff + coeffSum (ts ++ ys) = (t.coeff + coeffSum ts) + coeffSum ys
      rw [coeffSum_append ts ys]
      exact (Nat.add_assoc t.coeff (coeffSum ts) (coeffSum ys)).symm

theorem coeffSum_prependTerms (c : Nat) :
    forall ts : List PartialBellTerm,
      coeffSum (prependTerms c ts) = coeffSum ts
  | [] => rfl
  | t :: ts => by
      change t.coeff + coeffSum (prependTerms c ts) = t.coeff + coeffSum ts
      rw [coeffSum_prependTerms c ts]

theorem coeffSum_singletonTerms :
    forall ts : List PartialBellTerm,
      coeffSum (singletonTerms ts) = coeffSum ts
  | [] => rfl
  | t :: ts => by
      change t.coeff + coeffSum (singletonTerms ts) = t.coeff + coeffSum ts
      rw [coeffSum_singletonTerms ts]

theorem profileBlockCount_incFirst :
    forall p : List Nat, profileBlockCount (incFirst p) = Nat.succ (profileBlockCount p)
  | [] => rfl
  | c :: cs => by
      change Nat.succ c + profileBlockCount cs =
        Nat.succ (c + profileBlockCount cs)
      exact Nat.succ_add c (profileBlockCount cs)

theorem TermsHaveBlockCount_append {k : Nat} {xs ys : List PartialBellTerm} :
    TermsHaveBlockCount k xs -> TermsHaveBlockCount k ys ->
      TermsHaveBlockCount k (xs ++ ys) := by
  intro left right
  induction left with
  | nil =>
      exact right
  | cons head _tail ih =>
      exact TermsHaveBlockCount.cons head ih

theorem TermsHaveBlockCount_prependTerms (c k : Nat) :
    forall {ts : List PartialBellTerm},
      TermsHaveBlockCount k ts -> TermsHaveBlockCount (c + k) (prependTerms c ts)
  | [], TermsHaveBlockCount.nil =>
      TermsHaveBlockCount.nil
  | _t :: _ts, TermsHaveBlockCount.cons head tail => by
      apply TermsHaveBlockCount.cons
      · change c + profileBlockCount _t.profile = c + k
        rw [head]
      · exact TermsHaveBlockCount_prependTerms c k tail

theorem TermsHaveBlockCount_singletonTerms (k : Nat) :
    forall {ts : List PartialBellTerm},
      TermsHaveBlockCount k ts -> TermsHaveBlockCount (Nat.succ k) (singletonTerms ts)
  | [], TermsHaveBlockCount.nil =>
      TermsHaveBlockCount.nil
  | t :: _ts, TermsHaveBlockCount.cons head tail => by
      apply TermsHaveBlockCount.cons
      · change profileBlockCount (incFirst t.profile) = Nat.succ k
        rw [profileBlockCount_incFirst t.profile]
        rw [head]
      · exact TermsHaveBlockCount_singletonTerms k tail

theorem growProfile_blockCount (coeff : Nat) :
    forall p : List Nat, TermsHaveBlockCount (profileBlockCount p) (growProfile coeff p)
  | [] =>
      TermsHaveBlockCount.nil
  | 0 :: cs => by
      change TermsHaveBlockCount (0 + profileBlockCount cs)
        (prependTerms 0 (growProfile coeff cs))
      exact TermsHaveBlockCount_prependTerms 0 (profileBlockCount cs)
        (growProfile_blockCount coeff cs)
  | Nat.succ d :: cs => by
      change TermsHaveBlockCount (Nat.succ d + profileBlockCount cs)
        ({ coeff := coeff * Nat.succ d, profile := d :: incFirst cs } ::
          prependTerms (Nat.succ d) (growProfile coeff cs))
      apply TermsHaveBlockCount.cons
      · change d + profileBlockCount (incFirst cs) =
          Nat.succ d + profileBlockCount cs
        rw [profileBlockCount_incFirst cs]
        rw [Nat.add_succ]
        rw [Nat.succ_add]
      · exact TermsHaveBlockCount_prependTerms (Nat.succ d) (profileBlockCount cs)
          (growProfile_blockCount coeff cs)

theorem TermsHaveBlockCount_growTerms (k : Nat) :
    forall {ts : List PartialBellTerm},
      TermsHaveBlockCount k ts -> TermsHaveBlockCount k (growTerms ts)
  | [], TermsHaveBlockCount.nil =>
      TermsHaveBlockCount.nil
  | t :: ts, TermsHaveBlockCount.cons head tail => by
      change TermsHaveBlockCount k (growProfile t.coeff t.profile ++ growTerms ts)
      have headGrow : TermsHaveBlockCount k (growProfile t.coeff t.profile) := by
        have localGrow := growProfile_blockCount t.coeff t.profile
        rw [head] at localGrow
        exact localGrow
      exact TermsHaveBlockCount_append headGrow (TermsHaveBlockCount_growTerms k tail)

theorem partialBellTerms_blockCount (n k : Nat) :
    TermsHaveBlockCount k (partialBellTerms n k) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          apply TermsHaveBlockCount.cons
          · rfl
          · exact TermsHaveBlockCount.nil
      | succ _ =>
          exact TermsHaveBlockCount.nil
  | succ n ih =>
      cases k with
      | zero =>
          exact TermsHaveBlockCount.nil
      | succ k =>
          change TermsHaveBlockCount (Nat.succ k)
            (singletonTerms (partialBellTerms n k) ++
              growTerms (partialBellTerms n (Nat.succ k)))
          exact TermsHaveBlockCount_append
            (TermsHaveBlockCount_singletonTerms k (ih k))
            (TermsHaveBlockCount_growTerms (Nat.succ k) (ih (Nat.succ k)))

theorem coeffSum_growProfile (coeff : Nat) :
    forall p : List Nat,
      coeffSum (growProfile coeff p) = coeff * profileBlockCount p
  | [] => by
      change 0 = coeff * 0
      rw [Nat.mul_zero]
  | 0 :: cs => by
      change coeffSum (prependTerms 0 (growProfile coeff cs)) =
        coeff * (0 + profileBlockCount cs)
      rw [Nat.zero_add]
      rw [coeffSum_prependTerms 0 (growProfile coeff cs)]
      rw [coeffSum_growProfile coeff cs]
  | Nat.succ d :: cs => by
      change coeff * Nat.succ d +
          coeffSum (prependTerms (Nat.succ d) (growProfile coeff cs)) =
        coeff * (Nat.succ d + profileBlockCount cs)
      rw [coeffSum_prependTerms (Nat.succ d) (growProfile coeff cs)]
      rw [coeffSum_growProfile coeff cs]
      rw [Nat.mul_add]

theorem coeffSum_growTerms :
    forall ts : List PartialBellTerm, coeffSum (growTerms ts) = weightedBlockSum ts
  | [] => rfl
  | t :: ts => by
      change coeffSum (growProfile t.coeff t.profile ++ growTerms ts) =
        t.coeff * profileBlockCount t.profile + weightedBlockSum ts
      rw [coeffSum_append]
      rw [coeffSum_growProfile t.coeff t.profile]
      rw [coeffSum_growTerms ts]

theorem weightedBlockSum_const (k : Nat) :
    forall {ts : List PartialBellTerm},
      TermsHaveBlockCount k ts -> weightedBlockSum ts = k * coeffSum ts
  | [], TermsHaveBlockCount.nil => by
      change 0 = k * 0
      rw [Nat.mul_zero]
  | t :: ts, TermsHaveBlockCount.cons head tail => by
      change t.coeff * profileBlockCount t.profile + weightedBlockSum ts =
        k * (t.coeff + coeffSum ts)
      rw [head]
      rw [weightedBlockSum_const k tail]
      rw [Nat.mul_add]
      rw [Nat.mul_comm t.coeff k]

theorem partialBellCoeffSum_recurrence (n k : Nat) :
    coeffSum (partialBellTerms (Nat.succ n) (Nat.succ k)) =
      coeffSum (partialBellTerms n k) +
        Nat.succ k * coeffSum (partialBellTerms n (Nat.succ k)) := by
  change coeffSum
      (singletonTerms (partialBellTerms n k) ++
        growTerms (partialBellTerms n (Nat.succ k))) =
    coeffSum (partialBellTerms n k) +
      Nat.succ k * coeffSum (partialBellTerms n (Nat.succ k))
  rw [coeffSum_append]
  rw [coeffSum_singletonTerms]
  rw [coeffSum_growTerms]
  rw [weightedBlockSum_const (Nat.succ k) (partialBellTerms_blockCount n (Nat.succ k))]

theorem partialBellCoeffSum_stirlingSecond (n k : Nat) :
    coeffSum (partialBellTerms n k) = stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          rfl
      | succ _ =>
          rfl
  | succ n ih =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          rw [partialBellCoeffSum_recurrence n k]
          rw [ih k]
          rw [ih (Nat.succ k)]
          change stirlingSecond n k + Nat.succ k * stirlingSecond n (Nat.succ k) =
            Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k
          exact Nat.add_comm (stirlingSecond n k)
            (Nat.succ k * stirlingSecond n (Nat.succ k))

theorem partialBell_zero_zero (weights : Nat -> Nat) :
    partialBell weights 0 0 = 1 := by
  rfl

theorem partialBell_zero_succ (weights : Nat -> Nat) (k : Nat) :
    partialBell weights 0 (Nat.succ k) = 0 := by
  rfl

theorem partialBell_succ_zero (weights : Nat -> Nat) (n : Nat) :
    partialBell weights (Nat.succ n) 0 = 0 := by
  rfl

theorem partialBell_succ_succ_recurrence (weights : Nat -> Nat) (n k : Nat) :
    partialBell weights (Nat.succ n) (Nat.succ k) =
      termsEval weights (singletonTerms (partialBellTerms n k)) +
        termsEval weights (growTerms (partialBellTerms n (Nat.succ k))) := by
  unfold partialBell
  change termsEval weights
      (singletonTerms (partialBellTerms n k) ++
        growTerms (partialBellTerms n (Nat.succ k))) =
    termsEval weights (singletonTerms (partialBellTerms n k)) +
      termsEval weights (growTerms (partialBellTerms n (Nat.succ k)))
  exact termsEval_append weights (singletonTerms (partialBellTerms n k))
    (growTerms (partialBellTerms n (Nat.succ k)))

theorem partialBell_allOnes_stirlingSecond (n k : Nat) :
    partialBell (fun _ => 1) n k = stirlingSecond n k := by
  unfold partialBell
  rw [termsEval_allOnes]
  exact partialBellCoeffSum_stirlingSecond n k

theorem completeBellPrefix_allOnes_bellPrefix (n : Nat) :
    forall k : Nat,
      completeBellPrefix (fun _ => 1) n k =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k
  | 0 => by
      change partialBell (fun _ => 1) n 0 =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n 0
      rw [partialBell_allOnes_stirlingSecond n 0]
      rfl
  | Nat.succ k => by
      change completeBellPrefix (fun _ => 1) n k +
          partialBell (fun _ => 1) n (Nat.succ k) =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
          BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ k)
      rw [completeBellPrefix_allOnes_bellPrefix n k]
      rw [partialBell_allOnes_stirlingSecond n (Nat.succ k)]

theorem partialBell_completeBell (n : Nat) :
    completeBell (fun _ => 1) n = bellNumber n := by
  unfold completeBell bellNumber BEDC.Derived.BellNumberUp.bellNumber
  exact completeBellPrefix_allOnes_bellPrefix n n

theorem faaDiBrunoCoefficient_partialBell (weights : Nat -> Nat) (n k : Nat) :
    faaDiBrunoCoefficient weights n k = partialBell weights n k := by
  rfl

theorem faaDiBrunoCoefficient_allOnes_stirlingSecond (n k : Nat) :
    faaDiBrunoCoefficient (fun _ => 1) n k = stirlingSecond n k := by
  exact partialBell_allOnes_stirlingSecond n k

theorem PartialBellUp_constructive_export :
    (forall n k : Nat, partialBell (fun _ => 1) n k = stirlingSecond n k) /\
      (forall n : Nat, completeBell (fun _ => 1) n = bellNumber n) /\
      (forall weights : Nat -> Nat, forall n k : Nat,
        faaDiBrunoCoefficient weights n k = partialBell weights n k) := by
  constructor
  · intro n k
    exact partialBell_allOnes_stirlingSecond n k
  · constructor
    · intro n
      exact partialBell_completeBell n
    · intro weights n k
      exact faaDiBrunoCoefficient_partialBell weights n k

end BEDC.Derived.PartialBellUp

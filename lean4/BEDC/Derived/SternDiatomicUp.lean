import BEDC.Derived.GcdUp
import BEDC.Derived.SternBrocotTreeUp

namespace BEDC.Derived.SternDiatomicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp (NatOne)
open BEDC.Derived.GcdUp
open BEDC.Derived.SternBrocotTreeUp

def sternDouble : Nat -> Nat
  | 0 => 0
  | n + 1 => Nat.succ (Nat.succ (sternDouble n))

def sternHalf : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => sternHalf n + 1

def sternEven : Nat -> Bool
  | 0 => true
  | 1 => false
  | n + 2 => sternEven n

theorem sternHalf_double (n : Nat) :
    sternHalf (sternDouble n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold sternDouble
      unfold sternHalf
      exact congrArg Nat.succ ih

theorem sternEven_double (n : Nat) :
    sternEven (sternDouble n) = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold sternDouble
      unfold sternEven
      exact ih

theorem sternHalf_odd (n : Nat) :
    sternHalf (Nat.succ (sternDouble n)) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold sternDouble
      unfold sternHalf
      exact congrArg Nat.succ ih

theorem sternEven_odd (n : Nat) :
    sternEven (Nat.succ (sternDouble n)) = false := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold sternDouble
      unfold sternEven
      exact ih

private theorem sternHalf_double_tail (n : Nat) :
    sternHalf (sternDouble n + 2) = n + 1 := by
  change sternHalf (Nat.succ (Nat.succ (sternDouble n))) = Nat.succ n
  unfold sternHalf
  exact congrArg Nat.succ (sternHalf_double n)

private theorem sternEven_double_tail (n : Nat) :
    sternEven (sternDouble n + 2) = true := by
  change sternEven (Nat.succ (Nat.succ (sternDouble n))) = true
  unfold sternEven
  exact sternEven_double n

private theorem sternHalf_odd_tail (n : Nat) :
    sternHalf (sternDouble n + 1 + 2) = n + 1 := by
  change sternHalf (Nat.succ (Nat.succ (Nat.succ (sternDouble n)))) = Nat.succ n
  unfold sternHalf
  exact congrArg Nat.succ (sternHalf_odd n)

private theorem sternEven_odd_tail (n : Nat) :
    sternEven (sternDouble n + 1 + 2) = false := by
  change sternEven (Nat.succ (Nat.succ (Nat.succ (sternDouble n)))) = false
  unfold sternEven
  exact sternEven_odd n

theorem sternHalf_le_self : (n : Nat) -> sternHalf n <= n
  | 0 => Nat.le_refl 0
  | 1 => Nat.zero_le 1
  | n + 2 => by
      change sternHalf n + 1 <= n + 2
      exact Nat.succ_le_succ (Nat.le_succ_of_le (sternHalf_le_self n))

theorem sternHalf_lt_tail (n : Nat) :
    sternHalf (n + 2) < n + 2 := by
  change sternHalf n + 1 < n + 2
  exact Nat.succ_lt_succ (Nat.lt_succ_of_le (sternHalf_le_self n))

def fuscFuel : Nat -> Nat -> Nat
  | 0, _ => 0
  | _fuel + 1, 0 => 0
  | _fuel + 1, 1 => 1
  | fuel + 1, n + 2 =>
      if sternEven (n + 2) then
        fuscFuel fuel (sternHalf (n + 2))
      else
        fuscFuel fuel (sternHalf (n + 2)) +
          fuscFuel fuel (sternHalf (n + 2) + 1)

def fusc (n : Nat) : Nat :=
  fuscFuel (n + 1) n

theorem fuscFuel_zero (fuel : Nat) :
    fuscFuel fuel 0 = 0 := by
  cases fuel with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem fuscFuel_one (fuel : Nat) :
    fuscFuel (fuel + 1) 1 = 1 := by
  rfl

theorem fusc_zero :
    fusc 0 = 0 := by
  rfl

theorem fusc_one :
    fusc 1 = 1 := by
  rfl

theorem fuscFuel_tail_step (fuel n : Nat) :
    fuscFuel (fuel + 1) (n + 2) =
      if sternEven (n + 2) then
        fuscFuel fuel (sternHalf (n + 2))
      else
        fuscFuel fuel (sternHalf (n + 2)) +
          fuscFuel fuel (sternHalf (n + 2) + 1) := by
  rfl

theorem fuscFuel_even_positive (fuel n : Nat) :
    fuscFuel (fuel + 1) (sternDouble (n + 1)) =
      fuscFuel fuel (n + 1) := by
  change fuscFuel (fuel + 1) (sternDouble n + 2) =
    fuscFuel fuel (n + 1)
  rw [fuscFuel_tail_step, sternEven_double_tail, sternHalf_double_tail]
  exact if_pos rfl

theorem fuscFuel_odd_positive (fuel n : Nat) :
    fuscFuel (fuel + 1) (Nat.succ (sternDouble (n + 1))) =
      fuscFuel fuel (n + 1) + fuscFuel fuel (n + 2) := by
  change fuscFuel (fuel + 1) (sternDouble n + 1 + 2) =
    fuscFuel fuel (n + 1) + fuscFuel fuel ((n + 1) + 1)
  rw [fuscFuel_tail_step, sternEven_odd_tail, sternHalf_odd_tail]
  exact if_neg (fun h => by cases h)

abbrev NatHist : Type :=
  BHist

abbrev natZero : NatHist :=
  BHist.Empty

abbrev natOne : NatHist :=
  NatOne

private theorem natOne_unary :
    UnaryHistory natOne :=
  unary_e1_closed unary_empty

private theorem natOne_nonempty :
    hsame natOne BHist.Empty -> False := by
  intro same
  exact not_hsame_e1_empty same

private theorem append_right_nonempty {a b : NatHist} :
    (hsame b BHist.Empty -> False) ->
      hsame (append a b) BHist.Empty -> False := by
  intro bNonempty sumEmpty
  exact bNonempty (append_eq_empty_iff.mp sumEmpty).right

private theorem common_divisor_nonempty_of_nonempty_target {d n : NatHist} :
    NatDivides d n -> (hsame n BHist.Empty -> False) ->
      hsame d BHist.Empty -> False := by
  intro divides targetNonempty dEmpty
  cases dEmpty
  exact targetNonempty (NatDivides_empty_left_result_empty divides)

theorem NatGcd_zero_left_one :
    NatGcd natZero natOne natOne := by
  constructor
  · exact unary_empty
  · constructor
    · exact natOne_unary
    · constructor
      · exact natOne_unary
      · constructor
        · exact NatDivides_empty_right_iff.mpr natOne_unary
        · constructor
          · exact (NatDivides_reflexive_pair natOne_unary).right
          · intro d _dividesZero dividesOne
            exact dividesOne

theorem NatGcd_one_left {n : NatHist} :
    UnaryHistory n -> NatGcd natOne n natOne := by
  intro nUnary
  constructor
  · exact natOne_unary
  · constructor
    · exact nUnary
    · constructor
      · exact natOne_unary
      · constructor
        · exact (NatDivides_reflexive_pair natOne_unary).right
        · constructor
          · exact (NatDivides_reflexive_pair nUnary).left
          · intro d dividesOne _dividesN
            exact dividesOne

theorem NatGcd_symm {a b g : NatHist} :
    NatGcd a b g -> NatGcd b a g := by
  intro gcd
  constructor
  · exact NatGcd_right_unary gcd
  · constructor
    · exact NatGcd_left_unary gcd
    · constructor
      · exact NatGcd_result_unary gcd
      · constructor
        · exact NatGcd_dvd_right gcd
        · constructor
          · exact NatGcd_dvd_left gcd
          · intro d dividesB dividesA
            exact NatGcd_greatest gcd dividesA dividesB

theorem NatGcd_left_hsame_transport {a a' b g : NatHist} :
    hsame a a' -> NatGcd a b g -> NatGcd a' b g := by
  intro same gcd
  cases same
  exact gcd

private theorem NatGcd_right_append_left {a b g : NatHist} :
    (hsame b BHist.Empty -> False) -> NatGcd a b g ->
      NatGcd a (append a b) g := by
  intro bNonempty gcd
  have aUnary : UnaryHistory a := NatGcd_left_unary gcd
  have bUnary : UnaryHistory b := NatGcd_right_unary gcd
  have sumNonempty : hsame (append a b) BHist.Empty -> False :=
    append_right_nonempty bNonempty
  constructor
  · exact aUnary
  · constructor
    · exact unary_append_closed aUnary bUnary
    · constructor
      · exact NatGcd_result_unary gcd
      · constructor
        · exact NatGcd_dvd_left gcd
        · constructor
          · exact NatDivides_cont_closed
              (NatGcd_dvd_left gcd) (NatGcd_dvd_right gcd) (cont_intro rfl)
          · intro d dividesA dividesSum
            have dNonempty : hsame d BHist.Empty -> False :=
              common_divisor_nonempty_of_nonempty_target dividesSum sumNonempty
            have dividesB : NatDivides d b :=
              dvd_tail_of_dvd_sum (NatDivides_divisor_unary dividesA) dNonempty
                (NatAdd_append_self aUnary bUnary) dividesA dividesSum
            exact NatGcd_greatest gcd dividesA dividesB

private theorem NatGcd_append_left_right {a b g : NatHist} :
    (hsame b BHist.Empty -> False) -> NatGcd a b g ->
      NatGcd (append a b) b g := by
  intro bNonempty gcd
  have aUnary : UnaryHistory a := NatGcd_left_unary gcd
  have bUnary : UnaryHistory b := NatGcd_right_unary gcd
  have sumUnary : UnaryHistory (append a b) :=
    unary_append_closed aUnary bUnary
  have sumNonempty : hsame (append a b) BHist.Empty -> False :=
    append_right_nonempty bNonempty
  constructor
  · exact sumUnary
  · constructor
    · exact bUnary
    · constructor
      · exact NatGcd_result_unary gcd
      · constructor
        · exact NatDivides_cont_closed
            (NatGcd_dvd_left gcd) (NatGcd_dvd_right gcd) (cont_intro rfl)
        · constructor
          · exact NatGcd_dvd_right gcd
          · intro d dividesSum dividesB
            have dNonempty : hsame d BHist.Empty -> False :=
              common_divisor_nonempty_of_nonempty_target dividesSum sumNonempty
            have sameSum : hsame (append a b) (append b a) :=
              unary_append_comm aUnary bUnary
            have dividesCommuted : NatDivides d (append b a) :=
              (NatDivides_dividend_hsame_transport dividesSum sameSum).right
            have dividesA : NatDivides d a :=
              dvd_tail_of_dvd_sum (NatDivides_divisor_unary dividesB) dNonempty
                (NatAdd_append_self bUnary aUnary) dividesB dividesCommuted
            exact NatGcd_greatest gcd dividesA dividesB

structure SternPair where
  left : NatHist
  right : NatHist
  left_unary : UnaryHistory left
  right_unary : UnaryHistory right
  right_nonempty : hsame right BHist.Empty -> False

namespace SternPair

def coprime (p : SternPair) : Prop :=
  NatGcd p.left p.right natOne

def numerator (p : SternPair) : Nat :=
  bwordLength p.left

def denominator (p : SternPair) : Nat :=
  bwordLength p.right

def leftStep (p : SternPair) : SternPair :=
  { left := p.left
    right := append p.left p.right
    left_unary := p.left_unary
    right_unary := unary_append_closed p.left_unary p.right_unary
    right_nonempty := append_right_nonempty p.right_nonempty }

def rightStep (p : SternPair) : SternPair :=
  { left := append p.left p.right
    right := p.right
    left_unary := unary_append_closed p.left_unary p.right_unary
    right_unary := p.right_unary
    right_nonempty := p.right_nonempty }

theorem leftStep_coprime {p : SternPair} :
    p.coprime -> (leftStep p).coprime := by
  intro gcd
  exact NatGcd_right_append_left p.right_nonempty gcd

theorem rightStep_coprime {p : SternPair} :
    p.coprime -> (rightStep p).coprime := by
  intro gcd
  exact NatGcd_append_left_right p.right_nonempty gcd

theorem leftStep_readback (p : SternPair) :
    (leftStep p).numerator = p.numerator ∧
      (leftStep p).denominator = p.numerator + p.denominator := by
  constructor
  · rfl
  · unfold denominator numerator leftStep
    exact bwordLength_append p.left p.right

theorem rightStep_readback (p : SternPair) :
    (rightStep p).numerator = p.numerator + p.denominator ∧
      (rightStep p).denominator = p.denominator := by
  constructor
  · unfold numerator rightStep
    exact bwordLength_append p.left p.right
  · rfl

end SternPair

def sternRoot : SternPair :=
  { left := natZero
    right := natOne
    left_unary := unary_empty
    right_unary := natOne_unary
    right_nonempty := natOne_nonempty }

def sternPositiveRoot : SternPair :=
  { left := natOne
    right := natOne
    left_unary := natOne_unary
    right_unary := natOne_unary
    right_nonempty := natOne_nonempty }

theorem sternRoot_coprime :
    sternRoot.coprime := by
  exact NatGcd_zero_left_one

theorem sternPositiveRoot_coprime :
    sternPositiveRoot.coprime := by
  exact NatGcd_one_left natOne_unary

def sternIndexedPairFuel : Nat -> Nat -> SternPair
  | 0, _ => sternRoot
  | _fuel + 1, 0 => sternRoot
  | _fuel + 1, 1 => SternPair.rightStep sternRoot
  | fuel + 1, n + 2 =>
      if sternEven (n + 2) then
        SternPair.leftStep (sternIndexedPairFuel fuel (sternHalf (n + 2)))
      else
        SternPair.rightStep (sternIndexedPairFuel fuel (sternHalf (n + 2)))

def sternIndexedPair (n : Nat) : SternPair :=
  sternIndexedPairFuel (n + 1) n

def sternFusc (n : Nat) : Nat :=
  (sternIndexedPair n).numerator

def sternFuscNext (n : Nat) : Nat :=
  (sternIndexedPair n).denominator

theorem sternIndexedPairFuel_adjacent_coprime :
    (fuel n : Nat) -> (sternIndexedPairFuel fuel n).coprime
  | 0, _ => sternRoot_coprime
  | _fuel + 1, 0 => sternRoot_coprime
  | _fuel + 1, 1 => SternPair.rightStep_coprime sternRoot_coprime
  | fuel + 1, n + 2 => by
      unfold sternIndexedPairFuel
      cases h : sternEven (n + 2) with
      | false =>
          rw [if_neg (fun eqTrue => by cases eqTrue)]
          exact SternPair.rightStep_coprime
            (sternIndexedPairFuel_adjacent_coprime fuel (sternHalf (n + 2)))
      | true =>
          rw [if_pos rfl]
          exact SternPair.leftStep_coprime
            (sternIndexedPairFuel_adjacent_coprime fuel (sternHalf (n + 2)))

theorem sternIndexedPair_adjacent_coprime (n : Nat) :
    (sternIndexedPair n).coprime := by
  exact sternIndexedPairFuel_adjacent_coprime (n + 1) n

theorem sternFusc_adjacent_coprime (n : Nat) :
    NatGcd (sternIndexedPair n).left (sternIndexedPair n).right natOne := by
  exact sternIndexedPair_adjacent_coprime n

def sternBranchStep : Branch -> SternPair -> SternPair
  | Branch.left, p => p.leftStep
  | Branch.right, p => p.rightStep

def sternPairEvalFrom (root : SternPair) : BranchPath -> SternPair
  | [] => root
  | step :: tail => sternBranchStep step (sternPairEvalFrom root tail)

def sternPairEval : BranchPath -> SternPair :=
  sternPairEvalFrom sternRoot

def sternPositiveEval : BranchPath -> SternPair :=
  sternPairEvalFrom sternPositiveRoot

theorem sternBranchStep_coprime {step : Branch} {p : SternPair} :
    p.coprime -> (sternBranchStep step p).coprime := by
  intro gcd
  cases step with
  | left =>
      exact SternPair.leftStep_coprime gcd
  | right =>
      exact SternPair.rightStep_coprime gcd

theorem sternPairEvalFrom_coprime {root : SternPair} :
    root.coprime -> ∀ path : BranchPath, (sternPairEvalFrom root path).coprime := by
  intro rootGcd path
  induction path with
  | nil =>
      exact rootGcd
  | cons step tail ih =>
      exact sternBranchStep_coprime ih

theorem sternPairEval_adjacent_coprime (path : BranchPath) :
    (sternPairEval path).coprime := by
  exact sternPairEvalFrom_coprime sternRoot_coprime path

theorem sternPositiveEval_adjacent_coprime (path : BranchPath) :
    (sternPositiveEval path).coprime := by
  exact sternPairEvalFrom_coprime sternPositiveRoot_coprime path

theorem sternPositiveEval_calkinWilf_readback (path : BranchPath) :
    (sternPositiveEval path).numerator = cwNumerator (cwEval path) ∧
      (sternPositiveEval path).denominator = cwDenominator (cwEval path) := by
  induction path with
  | nil =>
      constructor
      · rfl
      · rfl
  | cons step tail ih =>
      cases step with
      | left =>
          have sternRead := SternPair.leftStep_readback (sternPositiveEval tail)
          have cwRead := cw_left_readback (cwEval tail)
          constructor
          · exact sternRead.left.trans (ih.left.trans cwRead.left.symm)
          · calc
              (sternPositiveEval (Branch.left :: tail)).denominator =
                  (sternPositiveEval tail).numerator +
                    (sternPositiveEval tail).denominator := sternRead.right
              _ = cwNumerator (cwEval tail) + cwDenominator (cwEval tail) := by
                    rw [ih.left, ih.right]
              _ = cwDenominator (cwEval (Branch.left :: tail)) := cwRead.right.symm
      | right =>
          have sternRead := SternPair.rightStep_readback (sternPositiveEval tail)
          have cwRead := cw_right_readback (cwEval tail)
          constructor
          · calc
              (sternPositiveEval (Branch.right :: tail)).numerator =
                  (sternPositiveEval tail).numerator +
                    (sternPositiveEval tail).denominator := sternRead.left
              _ = cwNumerator (cwEval tail) + cwDenominator (cwEval tail) := by
                    rw [ih.left, ih.right]
              _ = cwNumerator (cwEval (Branch.right :: tail)) := cwRead.left.symm
          · exact sternRead.right.trans (ih.right.trans cwRead.right.symm)

end BEDC.Derived.SternDiatomicUp

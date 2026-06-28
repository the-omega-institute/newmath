import BEDC.Derived.RationalUp

namespace BEDC.Derived.BeattySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.RationalUp

structure RatSlope where
  num : Nat
  den : Nat
  den_pos : den = 0 -> False

def RatSlope.toRatNum : RatSlope -> RatNum
  | ⟨num, den, den_pos⟩ =>
  { num := intOfNat (natToUnary num) (natToUnary_unary num)
    den := natToUnary den
    den_pos := by
      cases den with
      | zero =>
          exact False.elim (den_pos rfl)
      | succ d =>
          cases d with
          | zero =>
              exact Or.inr rfl
          | succ d =>
              exact Or.inl
                ⟨natToUnary (Nat.succ d), natToUnary_unary (Nat.succ d),
                  (fun empty => by cases empty),
                  by
                    change Cont (BHist.e1 BHist.Empty) (natToUnary (Nat.succ d))
                      (BHist.e1 (natToUnary (Nat.succ d)))
                    have appendNatOne :
                        append (BHist.e1 BHist.Empty) (natToUnary (Nat.succ d)) =
                          BHist.e1 (natToUnary (Nat.succ d)) :=
                      (unary_append_e1_left
                        (h := natToUnary (Nat.succ d)) (k := BHist.Empty)
                        (natToUnary_unary (Nat.succ d))).trans
                        (congrArg BHist.e1
                          (append_empty_left (natToUnary (Nat.succ d))))
                    exact cont_intro
                      appendNatOne.symm⟩ }

def ratSlope (num den : Nat) (den_pos : den = 0 -> False) : RatSlope :=
  { num := num, den := den, den_pos := den_pos }

def ratSlopeTwo : RatSlope :=
  ratSlope 2 1 (by intro h; cases h)

def ratSlopeFiveTwo : RatSlope :=
  ratSlope 5 2 (by intro h; cases h)

def ratSlopeFiveThree : RatSlope :=
  ratSlope 5 3 (by intro h; cases h)

def ratSlopeEightFifths : RatSlope :=
  ratSlope 8 5 (by intro h; cases h)

def ratSlopeEightThirds : RatSlope :=
  ratSlope 8 3 (by intro h; cases h)

def beatty (r : RatSlope) (n : Nat) : Nat :=
  (n * r.num) / r.den

def beattySeq (r : RatSlope) : Nat -> Nat :=
  fun n => beatty r n

def RayleighPair (r s : RatSlope) : Prop :=
  r.den * s.num + s.den * r.num = r.num * s.num

def positiveWindow : Nat -> List Nat
  | 0 => []
  | Nat.succ n => positiveWindow n ++ [Nat.succ n]

def beattyWindow (r : RatSlope) : Nat -> List Nat
  | 0 => []
  | Nat.succ n => beattyWindow r n ++ [beatty r (Nat.succ n)]

def boundaryCompanionBeatty (r : RatSlope) (n : Nat) : Nat :=
  (n * r.num - 1) / (r.num - r.den)

def boundaryCompanionWindow (r : RatSlope) : Nat -> List Nat
  | 0 => []
  | Nat.succ n =>
      boundaryCompanionWindow r n ++
        [boundaryCompanionBeatty r (Nat.succ n)]

def listCoversOnce (xs : List Nat) (k : Nat) : Prop :=
  List.count k xs = 1

def listAvoids (xs : List Nat) (k : Nat) : Prop :=
  List.count k xs = 0

def complementaryOnWindow (left right target : List Nat) : Prop :=
  ∀ k : Nat, List.count k target =
    List.count k left + List.count k right

def beattyComplementaryOnWindow (r s : RatSlope) (fuel : Nat) : Prop :=
  complementaryOnWindow (beattyWindow r fuel) (beattyWindow s fuel)
    (positiveWindow fuel)

def countOnceThroughSix (xs : List Nat) : Prop :=
  List.count 1 xs = 1 ∧
    List.count 2 xs = 1 ∧
    List.count 3 xs = 1 ∧
    List.count 4 xs = 1 ∧
    List.count 5 xs = 1 ∧
    List.count 6 xs = 1

def countOnceThroughFifteen (xs : List Nat) : Prop :=
  List.count 1 xs = 1 ∧
    List.count 2 xs = 1 ∧
    List.count 3 xs = 1 ∧
    List.count 4 xs = 1 ∧
    List.count 5 xs = 1 ∧
    List.count 6 xs = 1 ∧
    List.count 7 xs = 1 ∧
    List.count 8 xs = 1 ∧
    List.count 9 xs = 1 ∧
    List.count 10 xs = 1 ∧
    List.count 11 xs = 1 ∧
    List.count 12 xs = 1 ∧
    List.count 13 xs = 1 ∧
    List.count 14 xs = 1 ∧
    List.count 15 xs = 1

def overlapAt (r s : RatSlope) (n m value : Nat) : Prop :=
  beatty r n = value ∧ beatty s m = value

theorem beattySeq_apply (r : RatSlope) (n : Nat) :
    beattySeq r n = beatty r n := by
  rfl

theorem ratSlopeTwo_rat_carrier_den :
    (ratSlopeTwo.toRatNum).den = natToUnary 1 := by
  rfl

theorem ratSlopeFiveTwo_rat_carrier_den :
    (ratSlopeFiveTwo.toRatNum).den = natToUnary 2 := by
  rfl

theorem ratSlopeFiveThree_rat_carrier_den :
    (ratSlopeFiveThree.toRatNum).den = natToUnary 3 := by
  rfl

theorem ratSlopeEightFifths_rat_carrier_den :
    (ratSlopeEightFifths.toRatNum).den = natToUnary 5 := by
  rfl

theorem ratSlopeEightThirds_rat_carrier_den :
    (ratSlopeEightThirds.toRatNum).den = natToUnary 3 := by
  rfl

theorem beatty_two_first_overlap :
    overlapAt ratSlopeTwo ratSlopeTwo 1 1 2 := by
  exact And.intro rfl rfl

theorem beatty_two_rayleigh_sum :
    RayleighPair ratSlopeTwo ratSlopeTwo := by
  rfl

theorem beatty_five_pair_rayleigh_sum :
    RayleighPair ratSlopeFiveTwo ratSlopeFiveThree := by
  rfl

theorem beatty_five_two_values :
    beattyWindow ratSlopeFiveTwo 6 = [2, 5, 7, 10, 12, 15] := by
  rfl

theorem boundary_companion_five_two_values :
    boundaryCompanionWindow ratSlopeFiveTwo 9 =
      [1, 3, 4, 6, 8, 9, 11, 13, 14] := by
  rfl

theorem beatty_five_two_boundary_complement_counts :
    let xs :=
      beattyWindow ratSlopeFiveTwo 6 ++ boundaryCompanionWindow ratSlopeFiveTwo 9
    List.Nodup xs ∧ xs.length = 15 ∧ countOnceThroughFifteen xs := by
  change List.Nodup [2, 5, 7, 10, 12, 15, 1, 3, 4, 6, 8, 9, 11, 13, 14] ∧
    [2, 5, 7, 10, 12, 15, 1, 3, 4, 6, 8, 9, 11, 13, 14].length = 15 ∧
      countOnceThroughFifteen
        [2, 5, 7, 10, 12, 15, 1, 3, 4, 6, 8, 9, 11, 13, 14]
  unfold countOnceThroughFifteen
  decide

theorem beatty_two_not_complementary_at_two :
    List.count 2 (positiveWindow 2) = 1 ∧
      List.count 2 (beattyWindow ratSlopeTwo 2) +
          List.count 2 (beattyWindow ratSlopeTwo 2) = 2 := by
  exact And.intro rfl rfl

theorem beatty_eight_fifths_values :
    beattyWindow ratSlopeEightFifths 7 = [1, 3, 4, 6, 8, 9, 11] := by
  rfl

theorem beatty_eight_thirds_values :
    beattyWindow ratSlopeEightThirds 7 = [2, 5, 8, 10, 13, 16, 18] := by
  rfl

theorem beatty_eight_pair_rayleigh_sum :
    RayleighPair ratSlopeEightFifths ratSlopeEightThirds := by
  rfl

theorem beatty_eight_pair_window_gap_at_seven :
    List.count 7 (positiveWindow 7) = 1 ∧
      List.count 7 (beattyWindow ratSlopeEightFifths 7) = 0 ∧
      List.count 7 (beattyWindow ratSlopeEightThirds 7) = 0 := by
  exact And.intro rfl (And.intro rfl rfl)

theorem beatty_eight_pair_not_complementary_on_seven :
    beattyComplementaryOnWindow ratSlopeEightFifths ratSlopeEightThirds 7 -> False := by
  intro h
  have hseven := h 7
  change 1 = 0 at hseven
  cases hseven

theorem beatty_eight_pair_covers_each_once_to_six :
    countOnceThroughSix
      (beattyWindow ratSlopeEightFifths 6 ++
        beattyWindow ratSlopeEightThirds 6) := by
  change countOnceThroughSix [1, 3, 4, 6, 8, 9, 2, 5, 8, 10, 13, 16]
  unfold countOnceThroughSix
  decide

end BEDC.Derived.BeattySequenceUp

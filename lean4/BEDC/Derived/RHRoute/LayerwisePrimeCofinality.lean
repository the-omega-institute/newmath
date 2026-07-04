import BEDC.Derived.RHRoute.BedcZetaCriticalUnit

namespace BEDC.Derived.RHRoute.LayerwisePrimeCofinality

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.BedcZetaCriticalUnit

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BedcZetaCriticalUnit.RatComplex

abbrev NontrivialZetaZero :=
  BedcZetaCriticalUnit.NontrivialZetaZero

abbrev ConstructiveRH :=
  BedcZetaCriticalUnit.ConstructiveRH

private instance primeIntegerUpDecidableEq :
    DecidableEq BEDC.Derived.PrimeUp.IntegerUp := by
  intro x y
  cases x with
  | mk sx mx cx =>
      cases y with
      | mk sy my cy =>
          cases decEq sx sy with
          | isTrue hs =>
              cases decEq mx my with
              | isTrue hm =>
                  apply isTrue
                  cases hs
                  cases hm
                  have hc : cx = cy := proof_irrel cx cy
                  cases hc
                  rfl
              | isFalse hm =>
                  apply isFalse
                  intro h
                  cases h
                  exact hm rfl
          | isFalse hs =>
              apply isFalse
              intro h
              cases h
              exact hs rfl

private instance ratNumDecidableEq : DecidableEq RatNum := by
  intro x y
  cases x with
  | mk nx dx cx =>
      cases y with
      | mk ny dy cy =>
          cases decEq nx ny with
          | isTrue hn =>
              cases decEq dx dy with
              | isTrue hd =>
                  apply isTrue
                  cases hn
                  cases hd
                  have hc : cx = cy := proof_irrel cx cy
                  cases hc
                  rfl
              | isFalse hd =>
                  apply isFalse
                  intro h
                  cases h
                  exact hd rfl
          | isFalse hn =>
              apply isFalse
              intro h
              cases h
              exact hn rfl

def allZeroList (l : List RatNum) : Prop :=
  forall x : RatNum, List.Mem x l -> x = ratZero

theorem cofinal_separating
    (l : List RatNum)
    (h : Not (forall x : RatNum, List.Mem x l -> x = ratZero)) :
    Exists (fun x : RatNum =>
      And (List.Mem x l) (x = ratZero -> False)) := by
  induction l with
  | nil =>
      apply False.elim
      apply h
      intro x hx
      cases hx
  | cons head tail ih =>
      match decEq head ratZero with
      | isTrue hHead =>
          have hTail :
            Not (forall x : RatNum, List.Mem x tail -> x = ratZero) := by
            intro allTail
            apply h
            intro x hx
            cases hx with
            | head =>
                exact hHead
            | tail _ hxTail =>
                exact allTail x hxTail
          cases ih hTail with
          | intro x hx =>
              exact Exists.intro x
                (And.intro (List.Mem.tail head hx.left) hx.right)
      | isFalse hHead =>
          exact Exists.intro head (And.intro (List.Mem.head tail) hHead)

theorem allZeroList_not_of_member_ne
    {l : List RatNum} {x : RatNum} :
    List.Mem x l -> (x = ratZero -> False) -> Not (allZeroList l) := by
  intro hx hxNe allZero
  exact hxNe (allZero x hx)

theorem cofinal_separating_seq
    (v : Nat -> RatNum) (m : Nat) (h : v m = ratZero -> False) :
    Exists (fun k : Nat => v k = ratZero -> False) := by
  exact Exists.intro m h

def canonicalNonzeroReading : List RatNum :=
  [ratZero, ratOne]

theorem ratOne_ne_ratZero : ratOne = ratZero -> False := by
  intro h
  cases h

theorem canonicalNonzeroReading_not_all_zero :
    Not (forall x : RatNum,
      List.Mem x canonicalNonzeroReading -> x = ratZero) := by
  exact allZeroList_not_of_member_ne
    (by
      unfold canonicalNonzeroReading
      exact List.Mem.tail ratZero (List.Mem.head []))
    ratOne_ne_ratZero

theorem canonicalNonzeroReading_has_witness :
    Exists (fun x : RatNum =>
      And (List.Mem x canonicalNonzeroReading) (x = ratZero -> False)) :=
  cofinal_separating canonicalNonzeroReading
    canonicalNonzeroReading_not_all_zero

-- Legal closure has no hidden radial register: the normalized residual is
-- unit-radial, equivalently the critical offset is zero.
def NoHiddenRadialRegister : Prop :=
  BedcZetaCriticalUnit.CriticalUnitSoundness

-- Hilbert--Polya style source-side realization obligation: the zero-relevant
-- radial witness is embedded in the same classifier space and captures the
-- radial leg without presupposing zero offset.
inductive ZetaBEDCEmbedding : Prop

structure CofinalRHRoute where
  embedding : ZetaBEDCEmbedding
  noHiddenRadialRegister : NoHiddenRadialRegister

theorem cofinalRoute_imply_constructiveRH
    (R : CofinalRHRoute) :
    ConstructiveRH :=
  BedcZetaCriticalUnit.zetaBEDC_closure_imply_constructiveRH
    { criticalUnitSoundness := R.noHiddenRadialRegister }

end BEDC.Derived.RHRoute.LayerwisePrimeCofinality

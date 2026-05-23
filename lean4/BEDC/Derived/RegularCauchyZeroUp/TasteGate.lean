import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyZeroUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyZeroUp : Type where
  | mk (q s r m mu e h c p n : BHist) : RegularCauchyZeroUp
  deriving DecidableEq

def regularCauchyZeroEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyZeroEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyZeroEncodeBHist h

def regularCauchyZeroDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyZeroDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyZeroDecodeBHist tail)

private def regularCauchyZeroNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => regularCauchyZeroNthRawEvent tail n

private theorem regularCauchyZero_decode_encode_bhist :
    ∀ h : BHist, regularCauchyZeroDecodeBHist (regularCauchyZeroEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyZero_mk_congr
    {q q' s s' r r' m m' mu mu' e e' h h' c c' p p' n n' : BHist}
    (hq : q' = q)
    (hs : s' = s)
    (hr : r' = r)
    (hm : m' = m)
    (hmu : mu' = mu)
    (he : e' = e)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hn : n' = n) :
    RegularCauchyZeroUp.mk q' s' r' m' mu' e' h' c' p' n' =
      RegularCauchyZeroUp.mk q s r m mu e h c p n := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hq
  cases hs
  cases hr
  cases hm
  cases hmu
  cases he
  cases hh
  cases hc
  cases hp
  cases hn
  rfl

def regularCauchyZeroToEventFlow : RegularCauchyZeroUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyZeroUp.mk q s r m mu e h c p n =>
      [regularCauchyZeroEncodeBHist q,
        regularCauchyZeroEncodeBHist s,
        regularCauchyZeroEncodeBHist r,
        regularCauchyZeroEncodeBHist m,
        regularCauchyZeroEncodeBHist mu,
        regularCauchyZeroEncodeBHist e,
        regularCauchyZeroEncodeBHist h,
        regularCauchyZeroEncodeBHist c,
        regularCauchyZeroEncodeBHist p,
        regularCauchyZeroEncodeBHist n]

def regularCauchyZeroFromEventFlow (ef : EventFlow) : Option RegularCauchyZeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyZeroUp.mk
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 0))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 1))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 2))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 3))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 4))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 5))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 6))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 7))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 8))
      (regularCauchyZeroDecodeBHist (regularCauchyZeroNthRawEvent ef 9)))

private theorem regularCauchyZero_round_trip :
    ∀ x : RegularCauchyZeroUp,
      regularCauchyZeroFromEventFlow (regularCauchyZeroToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q s r m mu e h c p n =>
      exact
        congrArg some
          (regularCauchyZero_mk_congr
            (regularCauchyZero_decode_encode_bhist q)
            (regularCauchyZero_decode_encode_bhist s)
            (regularCauchyZero_decode_encode_bhist r)
            (regularCauchyZero_decode_encode_bhist m)
            (regularCauchyZero_decode_encode_bhist mu)
            (regularCauchyZero_decode_encode_bhist e)
            (regularCauchyZero_decode_encode_bhist h)
            (regularCauchyZero_decode_encode_bhist c)
            (regularCauchyZero_decode_encode_bhist p)
            (regularCauchyZero_decode_encode_bhist n))

private theorem regularCauchyZeroToEventFlow_injective {x y : RegularCauchyZeroUp} :
    regularCauchyZeroToEventFlow x = regularCauchyZeroToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyZeroFromEventFlow (regularCauchyZeroToEventFlow x) =
        regularCauchyZeroFromEventFlow (regularCauchyZeroToEventFlow y) :=
    congrArg regularCauchyZeroFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyZero_round_trip x).symm
      (Eq.trans hread (regularCauchyZero_round_trip y)))

instance regularCauchyZeroBHistCarrier : BHistCarrier RegularCauchyZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyZeroToEventFlow
  fromEventFlow := regularCauchyZeroFromEventFlow

instance regularCauchyZeroChapterTasteGate :
    ChapterTasteGate RegularCauchyZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyZeroFromEventFlow (regularCauchyZeroToEventFlow x) = some x
    exact regularCauchyZero_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyZeroToEventFlow_injective heq)

theorem RegularCauchyZeroTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyZeroUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyZeroUp) ∧
        (∀ h : BHist, regularCauchyZeroDecodeBHist (regularCauchyZeroEncodeBHist h) = h) ∧
          regularCauchyZeroEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regularCauchyZeroBHistCarrier⟩,
      ⟨regularCauchyZeroChapterTasteGate⟩,
      regularCauchyZero_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.RegularCauchyZeroUp.TasteGate

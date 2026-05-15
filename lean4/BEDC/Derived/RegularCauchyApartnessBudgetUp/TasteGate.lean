import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyApartnessBudgetUp : Type where
  | mk :
      (x a m w d r e h c p n : BHist) →
      RegularCauchyApartnessBudgetUp
  deriving DecidableEq

def regularCauchyApartnessBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyApartnessBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyApartnessBudgetEncodeBHist h

def regularCauchyApartnessBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyApartnessBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyApartnessBudgetDecodeBHist tail)

private theorem regularCauchyApartnessBudgetDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyApartnessBudgetDecodeBHist
        (regularCauchyApartnessBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyApartnessBudget_mk_congr
    {x x' a a' m m' w w' d d' r r' e e' h h' c c' p p' n n' : BHist}
    (hx : x' = x)
    (ha : a' = a)
    (hm : m' = m)
    (hw : w' = w)
    (hd : d' = d)
    (hr : r' = r)
    (he : e' = e)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hn : n' = n) :
    RegularCauchyApartnessBudgetUp.mk x' a' m' w' d' r' e' h' c' p' n' =
      RegularCauchyApartnessBudgetUp.mk x a m w d r e h c p n := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hx
  cases ha
  cases hm
  cases hw
  cases hd
  cases hr
  cases he
  cases hh
  cases hc
  cases hp
  cases hn
  rfl

def regularCauchyApartnessBudgetFields :
    RegularCauchyApartnessBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessBudgetUp.mk x a m w d r e h c p n =>
      [x, a, m, w, d, r, e, h, c, p, n]

def regularCauchyApartnessBudgetToEventFlow :
    RegularCauchyApartnessBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | pkt =>
      (regularCauchyApartnessBudgetFields pkt).map
        regularCauchyApartnessBudgetEncodeBHist

def regularCauchyApartnessBudgetFromEventFlow :
    EventFlow → Option RegularCauchyApartnessBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | x :: rest0 =>
      match rest0 with
      | [] => none
      | a :: rest1 =>
          match rest1 with
          | [] => none
          | m :: rest2 =>
              match rest2 with
              | [] => none
              | w :: rest3 =>
                  match rest3 with
                  | [] => none
                  | d :: rest4 =>
                      match rest4 with
                      | [] => none
                      | r :: rest5 =>
                          match rest5 with
                          | [] => none
                          | e :: rest6 =>
                              match rest6 with
                              | [] => none
                              | h :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | c :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | p :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | n :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RegularCauchyApartnessBudgetUp.mk
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        x)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        a)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        m)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        w)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        d)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        r)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        e)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        h)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        c)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        p)
                                                      (regularCauchyApartnessBudgetDecodeBHist
                                                        n))
                                              | _ :: _ => none

private theorem regularCauchyApartnessBudget_round_trip :
    ∀ pkt : RegularCauchyApartnessBudgetUp,
      regularCauchyApartnessBudgetFromEventFlow
        (regularCauchyApartnessBudgetToEventFlow pkt) = some pkt := by
  -- BEDC touchpoint anchor: BHist BMark
  intro pkt
  cases pkt with
  | mk x a m w d r e h c p n =>
      change
        some
          (RegularCauchyApartnessBudgetUp.mk
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist x))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist a))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist m))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist w))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist d))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist r))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist e))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist h))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist c))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist p))
            (regularCauchyApartnessBudgetDecodeBHist
              (regularCauchyApartnessBudgetEncodeBHist n))) =
          some (RegularCauchyApartnessBudgetUp.mk x a m w d r e h c p n)
      exact
        congrArg some
          (regularCauchyApartnessBudget_mk_congr
            (regularCauchyApartnessBudgetDecode_encode_bhist x)
            (regularCauchyApartnessBudgetDecode_encode_bhist a)
            (regularCauchyApartnessBudgetDecode_encode_bhist m)
            (regularCauchyApartnessBudgetDecode_encode_bhist w)
            (regularCauchyApartnessBudgetDecode_encode_bhist d)
            (regularCauchyApartnessBudgetDecode_encode_bhist r)
            (regularCauchyApartnessBudgetDecode_encode_bhist e)
            (regularCauchyApartnessBudgetDecode_encode_bhist h)
            (regularCauchyApartnessBudgetDecode_encode_bhist c)
            (regularCauchyApartnessBudgetDecode_encode_bhist p)
            (regularCauchyApartnessBudgetDecode_encode_bhist n))

private theorem regularCauchyApartnessBudgetToEventFlow_injective
    {x y : RegularCauchyApartnessBudgetUp} :
    regularCauchyApartnessBudgetToEventFlow x =
      regularCauchyApartnessBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyApartnessBudgetFromEventFlow
          (regularCauchyApartnessBudgetToEventFlow x) =
        regularCauchyApartnessBudgetFromEventFlow
          (regularCauchyApartnessBudgetToEventFlow y) :=
    congrArg regularCauchyApartnessBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyApartnessBudget_round_trip x).symm
      (Eq.trans hread (regularCauchyApartnessBudget_round_trip y)))

private theorem regularCauchyApartnessBudget_fields_faithful :
    ∀ x y : RegularCauchyApartnessBudgetUp,
      regularCauchyApartnessBudgetFields x =
        regularCauchyApartnessBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk x₁ a₁ m₁ w₁ d₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk x₂ a₂ m₂ w₂ d₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hx tail0
          injection tail0 with ha tail1
          injection tail1 with hm tail2
          injection tail2 with hw tail3
          injection tail3 with hd tail4
          injection tail4 with hr tail5
          injection tail5 with he tail6
          injection tail6 with hh tail7
          injection tail7 with hc tail8
          injection tail8 with hp tail9
          injection tail9 with hn _
          subst hx
          subst ha
          subst hm
          subst hw
          subst hd
          subst hr
          subst he
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance regularCauchyApartnessBudgetBHistCarrier :
    BHistCarrier RegularCauchyApartnessBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyApartnessBudgetToEventFlow
  fromEventFlow := regularCauchyApartnessBudgetFromEventFlow

instance regularCauchyApartnessBudgetChapterTasteGate :
    ChapterTasteGate RegularCauchyApartnessBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyApartnessBudgetFromEventFlow
        (regularCauchyApartnessBudgetToEventFlow x) = some x
    exact regularCauchyApartnessBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyApartnessBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyApartnessBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyApartnessBudgetChapterTasteGate

instance regularCauchyApartnessBudgetFieldFaithful :
    FieldFaithful RegularCauchyApartnessBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyApartnessBudgetFields
  field_faithful := regularCauchyApartnessBudget_fields_faithful

instance regularCauchyApartnessBudgetNontrivial :
    Nontrivial RegularCauchyApartnessBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyApartnessBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyApartnessBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyApartnessBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyApartnessBudgetDecodeBHist
          (regularCauchyApartnessBudgetEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyApartnessBudgetUp,
        regularCauchyApartnessBudgetFromEventFlow
          (regularCauchyApartnessBudgetToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyApartnessBudgetUp,
          regularCauchyApartnessBudgetToEventFlow x =
            regularCauchyApartnessBudgetToEventFlow y → x = y) ∧
          regularCauchyApartnessBudgetEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyApartnessBudgetDecode_encode_bhist
  · constructor
    · exact regularCauchyApartnessBudget_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyApartnessBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyApartnessBudgetUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoobUpcrossingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoobUpcrossingUp : Type where
  | mk (omega martingale lower upper horizon upcrossing expectation bound transports routes
      provenance nameCert : BHist) : DoobUpcrossingUp
  deriving DecidableEq

def doobUpcrossingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doobUpcrossingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doobUpcrossingEncodeBHist h

def doobUpcrossingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doobUpcrossingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doobUpcrossingDecodeBHist tail)

private theorem doobUpcrossingDecode_encode_bhist :
    ∀ h : BHist, doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def doobUpcrossingFields : DoobUpcrossingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoobUpcrossingUp.mk omega martingale lower upper horizon upcrossing expectation bound
      transports routes provenance nameCert =>
      [omega, martingale, lower, upper, horizon, upcrossing, expectation, bound, transports,
        routes, provenance, nameCert]

def doobUpcrossingToEventFlow : DoobUpcrossingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (doobUpcrossingFields x).map doobUpcrossingEncodeBHist

private def doobUpcrossingRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => doobUpcrossingRawAt n rest

def doobUpcrossingFromEventFlow (flow : EventFlow) : Option DoobUpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DoobUpcrossingUp.mk
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 0 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 1 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 2 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 3 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 4 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 5 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 6 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 7 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 8 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 9 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 10 flow))
      (doobUpcrossingDecodeBHist (doobUpcrossingRawAt 11 flow)))

private theorem doobUpcrossing_round_trip :
    ∀ x : DoobUpcrossingUp,
      doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk omega martingale lower upper horizon upcrossing expectation bound transports routes
      provenance nameCert =>
      change
        some
          (DoobUpcrossingUp.mk
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist omega))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist martingale))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist lower))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist upper))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist horizon))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist upcrossing))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist expectation))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist bound))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist transports))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist routes))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist provenance))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist nameCert))) =
          some
            (DoobUpcrossingUp.mk omega martingale lower upper horizon upcrossing expectation
              bound transports routes provenance nameCert)
      rw [doobUpcrossingDecode_encode_bhist omega,
        doobUpcrossingDecode_encode_bhist martingale,
        doobUpcrossingDecode_encode_bhist lower,
        doobUpcrossingDecode_encode_bhist upper,
        doobUpcrossingDecode_encode_bhist horizon,
        doobUpcrossingDecode_encode_bhist upcrossing,
        doobUpcrossingDecode_encode_bhist expectation,
        doobUpcrossingDecode_encode_bhist bound,
        doobUpcrossingDecode_encode_bhist transports,
        doobUpcrossingDecode_encode_bhist routes,
        doobUpcrossingDecode_encode_bhist provenance,
        doobUpcrossingDecode_encode_bhist nameCert]

private theorem doobUpcrossingToEventFlow_injective {x y : DoobUpcrossingUp} :
    doobUpcrossingToEventFlow x = doobUpcrossingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) =
        doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow y) :=
    congrArg doobUpcrossingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (doobUpcrossing_round_trip x).symm
      (Eq.trans hread (doobUpcrossing_round_trip y)))

private theorem doobUpcrossing_fields_faithful :
    ∀ x y : DoobUpcrossingUp, doobUpcrossingFields x = doobUpcrossingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk omega₁ martingale₁ lower₁ upper₁ horizon₁ upcrossing₁ expectation₁ bound₁
      transports₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk omega₂ martingale₂ lower₂ upper₂ horizon₂ upcrossing₂ expectation₂ bound₂
          transports₂ routes₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance doobUpcrossingBHistCarrier : BHistCarrier DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doobUpcrossingToEventFlow
  fromEventFlow := doobUpcrossingFromEventFlow

instance doobUpcrossingChapterTasteGate : ChapterTasteGate DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x
    exact doobUpcrossing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (doobUpcrossingToEventFlow_injective heq)

instance doobUpcrossingFieldFaithful : FieldFaithful DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doobUpcrossingFields
  field_faithful := doobUpcrossing_fields_faithful

def taste_gate : ChapterTasteGate DoobUpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doobUpcrossingChapterTasteGate

theorem DoobUpcrossingUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DoobUpcrossingUp) ∧
      (∀ h : BHist, doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist h) = h) ∧
        (∀ x : DoobUpcrossingUp,
          doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x) ∧
          (∀ x y : DoobUpcrossingUp,
            doobUpcrossingToEventFlow x = doobUpcrossingToEventFlow y → x = y) ∧
            doobUpcrossingEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              doobUpcrossingEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨doobUpcrossingChapterTasteGate⟩,
      doobUpcrossingDecode_encode_bhist,
      doobUpcrossing_round_trip,
      fun _ _ heq => doobUpcrossingToEventFlow_injective heq,
      rfl,
      rfl⟩

end BEDC.Derived.DoobUpcrossingUp

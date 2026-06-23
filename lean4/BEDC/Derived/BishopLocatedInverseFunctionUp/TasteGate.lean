import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedInverseFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedInverseFunctionUp : Type where
  | mk (continuous locatedApartness interval uniqueness existence stream regSeqRat dyadic
      realSeal transport replay provenance localCert : BHist) :
      BishopLocatedInverseFunctionUp
  deriving DecidableEq

def bishopLocatedInverseFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedInverseFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedInverseFunctionEncodeBHist h

def bishopLocatedInverseFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedInverseFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedInverseFunctionDecodeBHist tail)

private theorem bishopLocatedInverseFunction_decode_encode_bhist :
    ∀ h : BHist,
      bishopLocatedInverseFunctionDecodeBHist
        (bishopLocatedInverseFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopLocatedInverseFunctionFields :
    BishopLocatedInverseFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedInverseFunctionUp.mk continuous locatedApartness interval uniqueness
      existence stream regSeqRat dyadic realSeal transport replay provenance localCert =>
      [continuous, locatedApartness, interval, uniqueness, existence, stream, regSeqRat,
        dyadic, realSeal, transport, replay, provenance, localCert]

def bishopLocatedInverseFunctionToEventFlow :
    BishopLocatedInverseFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedInverseFunctionFields x).map bishopLocatedInverseFunctionEncodeBHist

private def bishopLocatedInverseFunctionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bishopLocatedInverseFunctionRawAt n rest

private def bishopLocatedInverseFunctionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => bishopLocatedInverseFunctionLengthEq n rest

def bishopLocatedInverseFunctionFromEventFlow :
    EventFlow → Option BishopLocatedInverseFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bishopLocatedInverseFunctionLengthEq 13 flow with
      | true =>
          some
            (BishopLocatedInverseFunctionUp.mk
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 0 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 1 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 2 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 3 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 4 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 5 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 6 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 7 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 8 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 9 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 10 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 11 flow))
              (bishopLocatedInverseFunctionDecodeBHist
                (bishopLocatedInverseFunctionRawAt 12 flow)))
      | false => none

private theorem bishopLocatedInverseFunction_round_trip :
    ∀ x : BishopLocatedInverseFunctionUp,
      bishopLocatedInverseFunctionFromEventFlow
          (bishopLocatedInverseFunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk continuous locatedApartness interval uniqueness existence stream regSeqRat dyadic
      realSeal transport replay provenance localCert =>
      change
        some
          (BishopLocatedInverseFunctionUp.mk
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist continuous))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist locatedApartness))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist interval))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist uniqueness))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist existence))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist stream))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist regSeqRat))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist dyadic))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist realSeal))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist transport))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist replay))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist provenance))
            (bishopLocatedInverseFunctionDecodeBHist
              (bishopLocatedInverseFunctionEncodeBHist localCert))) =
          some
            (BishopLocatedInverseFunctionUp.mk continuous locatedApartness interval uniqueness
              existence stream regSeqRat dyadic realSeal transport replay provenance
              localCert)
      exact congrArg some
        (by
          rw [bishopLocatedInverseFunction_decode_encode_bhist continuous,
            bishopLocatedInverseFunction_decode_encode_bhist locatedApartness,
            bishopLocatedInverseFunction_decode_encode_bhist interval,
            bishopLocatedInverseFunction_decode_encode_bhist uniqueness,
            bishopLocatedInverseFunction_decode_encode_bhist existence,
            bishopLocatedInverseFunction_decode_encode_bhist stream,
            bishopLocatedInverseFunction_decode_encode_bhist regSeqRat,
            bishopLocatedInverseFunction_decode_encode_bhist dyadic,
            bishopLocatedInverseFunction_decode_encode_bhist realSeal,
            bishopLocatedInverseFunction_decode_encode_bhist transport,
            bishopLocatedInverseFunction_decode_encode_bhist replay,
            bishopLocatedInverseFunction_decode_encode_bhist provenance,
            bishopLocatedInverseFunction_decode_encode_bhist localCert])

private theorem bishopLocatedInverseFunctionToEventFlow_injective
    {x y : BishopLocatedInverseFunctionUp} :
    bishopLocatedInverseFunctionToEventFlow x =
      bishopLocatedInverseFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedInverseFunctionFromEventFlow
          (bishopLocatedInverseFunctionToEventFlow x) =
        bishopLocatedInverseFunctionFromEventFlow
          (bishopLocatedInverseFunctionToEventFlow y) :=
    congrArg bishopLocatedInverseFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bishopLocatedInverseFunction_round_trip x).symm
      (Eq.trans hread (bishopLocatedInverseFunction_round_trip y)))

private theorem bishopLocatedInverseFunction_fields :
    ∀ x y : BishopLocatedInverseFunctionUp,
      bishopLocatedInverseFunctionFields x =
        bishopLocatedInverseFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk continuous₁ locatedApartness₁ interval₁ uniqueness₁ existence₁ stream₁
      regSeqRat₁ dyadic₁ realSeal₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk continuous₂ locatedApartness₂ interval₂ uniqueness₂ existence₂ stream₂
          regSeqRat₂ dyadic₂ realSeal₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases hfields
          rfl

instance bishopLocatedInverseFunctionBHistCarrier :
    BHistCarrier BishopLocatedInverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedInverseFunctionToEventFlow
  fromEventFlow := bishopLocatedInverseFunctionFromEventFlow

instance bishopLocatedInverseFunctionChapterTasteGate :
    ChapterTasteGate BishopLocatedInverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact bishopLocatedInverseFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedInverseFunctionToEventFlow_injective heq)

instance bishopLocatedInverseFunctionFieldFaithful :
    FieldFaithful BishopLocatedInverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedInverseFunctionFields
  field_faithful := bishopLocatedInverseFunction_fields

instance bishopLocatedInverseFunctionNontrivial :
    Nontrivial BishopLocatedInverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedInverseFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BishopLocatedInverseFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedInverseFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedInverseFunctionChapterTasteGate

theorem BishopLocatedInverseFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedInverseFunctionDecodeBHist
        (bishopLocatedInverseFunctionEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedInverseFunctionUp,
        bishopLocatedInverseFunctionFromEventFlow
          (bishopLocatedInverseFunctionToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedInverseFunctionUp,
          bishopLocatedInverseFunctionToEventFlow x =
            bishopLocatedInverseFunctionToEventFlow y → x = y) ∧
          bishopLocatedInverseFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bishopLocatedInverseFunction_decode_encode_bhist,
      bishopLocatedInverseFunction_round_trip,
      (fun _ _ heq => bishopLocatedInverseFunctionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopLocatedInverseFunctionUp

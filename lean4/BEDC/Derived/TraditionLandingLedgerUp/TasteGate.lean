import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraditionLandingLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraditionLandingLedgerUp : Type where
  | mk (S T R D H C P N : BHist) : TraditionLandingLedgerUp
  deriving DecidableEq

def traditionLandingLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traditionLandingLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traditionLandingLedgerEncodeBHist h

def traditionLandingLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traditionLandingLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traditionLandingLedgerDecodeBHist tail)

private theorem traditionLandingLedger_decode_encode_bhist :
    ∀ h : BHist,
      traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem traditionLandingLedger_mk_congr
    {S S' T T' R R' D D' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hT : T' = T)
    (hR : R' = R)
    (hD : D' = D)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    TraditionLandingLedgerUp.mk S' T' R' D' H' C' P' N' =
      TraditionLandingLedgerUp.mk S T R D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hT
  cases hR
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def traditionLandingLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => traditionLandingLedgerRawAt n rest

def traditionLandingLedgerFields : TraditionLandingLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionLandingLedgerUp.mk S T R D H C P N => [S, T, R, D, H, C, P, N]

def traditionLandingLedgerToEventFlow : TraditionLandingLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map traditionLandingLedgerEncodeBHist (traditionLandingLedgerFields x)

def traditionLandingLedgerFromEventFlow (ef : EventFlow) : Option TraditionLandingLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TraditionLandingLedgerUp.mk
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 0 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 1 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 2 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 3 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 4 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 5 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 6 ef))
      (traditionLandingLedgerDecodeBHist (traditionLandingLedgerRawAt 7 ef)))

private theorem traditionLandingLedger_round_trip :
    ∀ x : TraditionLandingLedgerUp,
      traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T R D H C P N =>
      change
        some
          (TraditionLandingLedgerUp.mk
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist S))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist T))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist R))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist D))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist H))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist C))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist P))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist N))) =
          some (TraditionLandingLedgerUp.mk S T R D H C P N)
      exact
        congrArg some
          (traditionLandingLedger_mk_congr
            (traditionLandingLedger_decode_encode_bhist S)
            (traditionLandingLedger_decode_encode_bhist T)
            (traditionLandingLedger_decode_encode_bhist R)
            (traditionLandingLedger_decode_encode_bhist D)
            (traditionLandingLedger_decode_encode_bhist H)
            (traditionLandingLedger_decode_encode_bhist C)
            (traditionLandingLedger_decode_encode_bhist P)
            (traditionLandingLedger_decode_encode_bhist N))

private theorem traditionLandingLedgerToEventFlow_injective {x y : TraditionLandingLedgerUp} :
    traditionLandingLedgerToEventFlow x = traditionLandingLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) =
        traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow y) :=
    congrArg traditionLandingLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (traditionLandingLedger_round_trip x).symm
      (Eq.trans hread (traditionLandingLedger_round_trip y)))

private theorem traditionLandingLedger_field_faithful :
    ∀ x y : TraditionLandingLedgerUp,
      traditionLandingLedgerFields x = traditionLandingLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 T1 R1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 R2 D2 H2 C2 P2 N2 =>
          cases h
          rfl

instance traditionLandingLedgerBHistCarrier : BHistCarrier TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traditionLandingLedgerToEventFlow
  fromEventFlow := traditionLandingLedgerFromEventFlow

instance traditionLandingLedgerChapterTasteGate :
    ChapterTasteGate TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) = some x
    exact traditionLandingLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (traditionLandingLedgerToEventFlow_injective heq)

instance traditionLandingLedgerFieldFaithful : FieldFaithful TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traditionLandingLedgerFields
  field_faithful := traditionLandingLedger_field_faithful

instance traditionLandingLedgerNontrivial : Nontrivial TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraditionLandingLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TraditionLandingLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TraditionLandingLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  traditionLandingLedgerChapterTasteGate

theorem TraditionLandingLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist h) = h) ∧
      (∀ x : TraditionLandingLedgerUp,
        traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : TraditionLandingLedgerUp,
          traditionLandingLedgerToEventFlow x = traditionLandingLedgerToEventFlow y →
            x = y) ∧
          traditionLandingLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : TraditionLandingLedgerUp,
              traditionLandingLedgerFields x = traditionLandingLedgerFields y → x = y) ∧
              (∃ x y : TraditionLandingLedgerUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨traditionLandingLedger_decode_encode_bhist,
      ⟨traditionLandingLedger_round_trip,
        ⟨fun _x _y heq => traditionLandingLedgerToEventFlow_injective heq,
          ⟨rfl,
            ⟨traditionLandingLedger_field_faithful,
              ⟨TraditionLandingLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                TraditionLandingLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩⟩⟩⟩⟩⟩

end BEDC.Derived.TraditionLandingLedgerUp

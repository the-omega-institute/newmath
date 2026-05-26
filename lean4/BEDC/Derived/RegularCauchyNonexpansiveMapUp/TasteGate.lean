import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNonexpansiveMapUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNonexpansiveMapUp : Type where
  | mk (Msrc Mtgt L Rin Win Wout D Rout E H C P N : BHist) :
      RegularCauchyNonexpansiveMapUp

def regularCauchyNonexpansiveMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNonexpansiveMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNonexpansiveMapEncodeBHist h

def regularCauchyNonexpansiveMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNonexpansiveMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNonexpansiveMapDecodeBHist tail)

private theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyNonexpansiveMapDecodeBHist
        (regularCauchyNonexpansiveMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyNonexpansiveMapFields :
    RegularCauchyNonexpansiveMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNonexpansiveMapUp.mk Msrc Mtgt L Rin Win Wout D Rout E H C P N =>
      [Msrc, Mtgt, L, Rin, Win, Wout, D, Rout, E, H, C, P, N]

def regularCauchyNonexpansiveMapToEventFlow :
    RegularCauchyNonexpansiveMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyNonexpansiveMapFields x).map regularCauchyNonexpansiveMapEncodeBHist

private def regularCauchyNonexpansiveMapRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyNonexpansiveMapRawAt n rest

private def regularCauchyNonexpansiveMapLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyNonexpansiveMapLengthEq n rest

def regularCauchyNonexpansiveMapFromEventFlow :
    EventFlow → Option RegularCauchyNonexpansiveMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyNonexpansiveMapLengthEq 13 flow with
      | true =>
          some
            (RegularCauchyNonexpansiveMapUp.mk
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 0 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 1 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 2 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 3 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 4 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 5 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 6 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 7 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 8 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 9 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 10 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 11 flow))
              (regularCauchyNonexpansiveMapDecodeBHist
                (regularCauchyNonexpansiveMapRawAt 12 flow)))
      | false => none

private theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_mk_congr
    {Msrc Msrc' Mtgt Mtgt' L L' Rin Rin' Win Win' Wout Wout' D D' Rout Rout'
      E E' H H' C C' P P' N N' : BHist}
    (hMsrc : Msrc' = Msrc) (hMtgt : Mtgt' = Mtgt) (hL : L' = L)
    (hRin : Rin' = Rin) (hWin : Win' = Win) (hWout : Wout' = Wout)
    (hD : D' = D) (hRout : Rout' = Rout) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyNonexpansiveMapUp.mk Msrc' Mtgt' L' Rin' Win' Wout' D'
        Rout' E' H' C' P' N' =
      RegularCauchyNonexpansiveMapUp.mk Msrc Mtgt L Rin Win Wout D Rout E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMsrc
  cases hMtgt
  cases hL
  cases hRin
  cases hWin
  cases hWout
  cases hD
  cases hRout
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyNonexpansiveMapUp,
      regularCauchyNonexpansiveMapFromEventFlow
        (regularCauchyNonexpansiveMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Msrc Mtgt L Rin Win Wout D Rout E H C P N =>
      change
        some
          (RegularCauchyNonexpansiveMapUp.mk
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Msrc))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Mtgt))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist L))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Rin))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Win))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Wout))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist D))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist Rout))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist E))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist H))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist C))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist P))
            (regularCauchyNonexpansiveMapDecodeBHist
              (regularCauchyNonexpansiveMapEncodeBHist N))) =
          some
            (RegularCauchyNonexpansiveMapUp.mk Msrc Mtgt L Rin Win Wout D Rout E H C P N)
      rw [RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Msrc,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Mtgt,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Rin,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Win,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Wout,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode Rout,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyNonexpansiveMapUp} :
    regularCauchyNonexpansiveMapToEventFlow x =
      regularCauchyNonexpansiveMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNonexpansiveMapFromEventFlow
          (regularCauchyNonexpansiveMapToEventFlow x) =
        regularCauchyNonexpansiveMapFromEventFlow
          (regularCauchyNonexpansiveMapToEventFlow y) :=
    congrArg regularCauchyNonexpansiveMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyNonexpansiveMapUp,
      regularCauchyNonexpansiveMapFields x =
        regularCauchyNonexpansiveMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Msrc Mtgt L Rin Win Wout D Rout E H C P N =>
      cases y with
      | mk Msrc' Mtgt' L' Rin' Win' Wout' D' Rout' E' H' C' P' N' =>
          cases hfields
          rfl

instance regularCauchyNonexpansiveMapBHistCarrier :
    BHistCarrier RegularCauchyNonexpansiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNonexpansiveMapToEventFlow
  fromEventFlow := regularCauchyNonexpansiveMapFromEventFlow

instance regularCauchyNonexpansiveMapChapterTasteGate :
    ChapterTasteGate RegularCauchyNonexpansiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNonexpansiveMapFromEventFlow
      (regularCauchyNonexpansiveMapToEventFlow x) = some x
    exact RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyNonexpansiveMapFieldFaithful :
    FieldFaithful RegularCauchyNonexpansiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyNonexpansiveMapFields
  field_faithful :=
    RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyNonexpansiveMapNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyNonexpansiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyNonexpansiveMapUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyNonexpansiveMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyNonexpansiveMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyNonexpansiveMapChapterTasteGate

theorem RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyNonexpansiveMapUp) ∧
      Nonempty (FieldFaithful RegularCauchyNonexpansiveMapUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyNonexpansiveMapUp) ∧
      (∀ h : BHist,
        regularCauchyNonexpansiveMapDecodeBHist
          (regularCauchyNonexpansiveMapEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyNonexpansiveMapUp,
        regularCauchyNonexpansiveMapFromEventFlow
          (regularCauchyNonexpansiveMapToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyNonexpansiveMapUp,
        regularCauchyNonexpansiveMapToEventFlow x =
          regularCauchyNonexpansiveMapToEventFlow y → x = y) ∧
      regularCauchyNonexpansiveMapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyNonexpansiveMapChapterTasteGate⟩
  constructor
  · exact ⟨regularCauchyNonexpansiveMapFieldFaithful⟩
  constructor
  · exact ⟨regularCauchyNonexpansiveMapNontrivial⟩
  constructor
  · exact RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact
      RegularCauchyNonexpansiveMapTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.RegularCauchyNonexpansiveMapUp

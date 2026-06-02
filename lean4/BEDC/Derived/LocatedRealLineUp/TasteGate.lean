import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealLineUp : Type where
  | mk (L A Q R S D H C P N : BHist) : LocatedRealLineUp
  deriving DecidableEq

def locatedRealLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealLineEncodeBHist h

def locatedRealLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealLineDecodeBHist tail)

private theorem locatedRealLine_decode_encode_bhist :
    ∀ h : BHist, locatedRealLineDecodeBHist (locatedRealLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealLineFields : LocatedRealLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealLineUp.mk L A Q R S D H C P N => [L, A, Q, R, S, D, H, C, P, N]

def locatedRealLineToEventFlow : LocatedRealLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealLineFields x).map locatedRealLineEncodeBHist

def locatedRealLineFromEventFlow : EventFlow → Option LocatedRealLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | L :: restL =>
        match restL with
        | [] => none
        | A :: restA =>
            match restA with
            | [] => none
            | Q :: restQ =>
                match restQ with
                | [] => none
                | R :: restR =>
                    match restR with
                    | [] => none
                    | S :: restS =>
                        match restS with
                        | [] => none
                        | D :: restD =>
                            match restD with
                            | [] => none
                            | H :: restH =>
                                match restH with
                                | [] => none
                                | C :: restC =>
                                    match restC with
                                    | [] => none
                                    | P :: restP =>
                                        match restP with
                                        | [] => none
                                        | N :: restN =>
                                            match restN with
                                            | [] =>
                                                some
                                                  (LocatedRealLineUp.mk
                                                    (locatedRealLineDecodeBHist L)
                                                    (locatedRealLineDecodeBHist A)
                                                    (locatedRealLineDecodeBHist Q)
                                                    (locatedRealLineDecodeBHist R)
                                                    (locatedRealLineDecodeBHist S)
                                                    (locatedRealLineDecodeBHist D)
                                                    (locatedRealLineDecodeBHist H)
                                                    (locatedRealLineDecodeBHist C)
                                                    (locatedRealLineDecodeBHist P)
                                                    (locatedRealLineDecodeBHist N))
                                            | _ :: _ => none

private theorem locatedRealLine_round_trip :
    ∀ x : LocatedRealLineUp,
      locatedRealLineFromEventFlow (locatedRealLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L A Q R S D H C P N =>
      change
        some
          (LocatedRealLineUp.mk
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist L))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist A))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist Q))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist R))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist S))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist D))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist H))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist C))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist P))
            (locatedRealLineDecodeBHist (locatedRealLineEncodeBHist N))) =
          some (LocatedRealLineUp.mk L A Q R S D H C P N)
      rw [locatedRealLine_decode_encode_bhist L, locatedRealLine_decode_encode_bhist A,
        locatedRealLine_decode_encode_bhist Q, locatedRealLine_decode_encode_bhist R,
        locatedRealLine_decode_encode_bhist S, locatedRealLine_decode_encode_bhist D,
        locatedRealLine_decode_encode_bhist H, locatedRealLine_decode_encode_bhist C,
        locatedRealLine_decode_encode_bhist P, locatedRealLine_decode_encode_bhist N]

private theorem locatedRealLineToEventFlow_injective {x y : LocatedRealLineUp} :
    locatedRealLineToEventFlow x = locatedRealLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealLineFromEventFlow (locatedRealLineToEventFlow x) =
        locatedRealLineFromEventFlow (locatedRealLineToEventFlow y) :=
    congrArg locatedRealLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealLine_round_trip x).symm
      (Eq.trans hread (locatedRealLine_round_trip y)))

instance locatedRealLineBHistCarrier : BHistCarrier LocatedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealLineToEventFlow
  fromEventFlow := locatedRealLineFromEventFlow

instance locatedRealLineChapterTasteGate : ChapterTasteGate LocatedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealLineFromEventFlow (locatedRealLineToEventFlow x) = some x
    exact locatedRealLine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealLineToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealLineChapterTasteGate

theorem LocatedRealLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRealLineDecodeBHist (locatedRealLineEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedRealLineUp) ∧
        Nonempty (ChapterTasteGate LocatedRealLineUp) ∧
          locatedRealLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedRealLine_decode_encode_bhist,
      ⟨locatedRealLineBHistCarrier⟩,
      ⟨locatedRealLineChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedRealLineUp

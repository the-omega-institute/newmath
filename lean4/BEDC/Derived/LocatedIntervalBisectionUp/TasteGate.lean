import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalBisectionUp : Type where
  | mk (I D M S W R H C P N : BHist) : LocatedIntervalBisectionUp
  deriving DecidableEq

def locatedIntervalBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalBisectionEncodeBHist h

def locatedIntervalBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalBisectionDecodeBHist tail)

private theorem locatedIntervalBisectionDecode_encode_bhist :
    ∀ h : BHist,
      locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalBisectionFields : LocatedIntervalBisectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalBisectionUp.mk I D M S W R H C P N => [I, D, M, S, W, R, H, C, P, N]

def locatedIntervalBisectionToEventFlow : LocatedIntervalBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedIntervalBisectionFields x).map locatedIntervalBisectionEncodeBHist

def locatedIntervalBisectionFromEventFlow : EventFlow → Option LocatedIntervalBisectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restD =>
      match restD with
      | [] => none
      | D :: restM =>
          match restM with
          | [] => none
          | M :: restS =>
              match restS with
              | [] => none
              | S :: restW =>
                  match restW with
                  | [] => none
                  | W :: restR =>
                      match restR with
                      | [] => none
                      | R :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (LocatedIntervalBisectionUp.mk
                                                  (locatedIntervalBisectionDecodeBHist I)
                                                  (locatedIntervalBisectionDecodeBHist D)
                                                  (locatedIntervalBisectionDecodeBHist M)
                                                  (locatedIntervalBisectionDecodeBHist S)
                                                  (locatedIntervalBisectionDecodeBHist W)
                                                  (locatedIntervalBisectionDecodeBHist R)
                                                  (locatedIntervalBisectionDecodeBHist H)
                                                  (locatedIntervalBisectionDecodeBHist C)
                                                  (locatedIntervalBisectionDecodeBHist P)
                                                  (locatedIntervalBisectionDecodeBHist N))
                                          | _ :: _ => none

private theorem locatedIntervalBisection_round_trip :
    ∀ x : LocatedIntervalBisectionUp,
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D M S W R H C P N =>
      change
        some
          (LocatedIntervalBisectionUp.mk
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist I))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist D))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist M))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist S))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist W))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist R))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist H))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist C))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist P))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist N))) =
          some (LocatedIntervalBisectionUp.mk I D M S W R H C P N)
      rw [locatedIntervalBisectionDecode_encode_bhist I,
        locatedIntervalBisectionDecode_encode_bhist D,
        locatedIntervalBisectionDecode_encode_bhist M,
        locatedIntervalBisectionDecode_encode_bhist S,
        locatedIntervalBisectionDecode_encode_bhist W,
        locatedIntervalBisectionDecode_encode_bhist R,
        locatedIntervalBisectionDecode_encode_bhist H,
        locatedIntervalBisectionDecode_encode_bhist C,
        locatedIntervalBisectionDecode_encode_bhist P,
        locatedIntervalBisectionDecode_encode_bhist N]

private theorem locatedIntervalBisectionToEventFlow_injective
    {x y : LocatedIntervalBisectionUp} :
    locatedIntervalBisectionToEventFlow x = locatedIntervalBisectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) =
        locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow y) :=
    congrArg locatedIntervalBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalBisection_round_trip x).symm
      (Eq.trans hread (locatedIntervalBisection_round_trip y)))

instance locatedIntervalBisectionBHistCarrier : BHistCarrier LocatedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalBisectionToEventFlow
  fromEventFlow := locatedIntervalBisectionFromEventFlow

instance locatedIntervalBisectionChapterTasteGate :
    ChapterTasteGate LocatedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x
    exact locatedIntervalBisection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalBisectionToEventFlow_injective heq)

theorem LocatedIntervalBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalBisectionUp,
        locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalBisectionUp,
          locatedIntervalBisectionToEventFlow x = locatedIntervalBisectionToEventFlow y → x = y) ∧
          locatedIntervalBisectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedIntervalBisectionDecode_encode_bhist,
      locatedIntervalBisection_round_trip,
      (fun _ _ heq => locatedIntervalBisectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedIntervalBisectionUp

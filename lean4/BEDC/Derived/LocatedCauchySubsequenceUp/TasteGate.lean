import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchySubsequenceUp : Type where
  | mk (M I D W R E H C P N : BHist) : LocatedCauchySubsequenceUp
  deriving DecidableEq

def locatedCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchySubsequenceEncodeBHist h

def locatedCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchySubsequenceDecodeBHist tail)

private theorem LocatedCauchySubsequenceUp_decode :
    ∀ h : BHist,
      locatedCauchySubsequenceDecodeBHist (locatedCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchySubsequenceFields :
    LocatedCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchySubsequenceUp.mk M I D W R E H C P N => [M, I, D, W, R, E, H, C, P, N]

def locatedCauchySubsequenceToEventFlow :
    LocatedCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchySubsequenceFields x).map locatedCauchySubsequenceEncodeBHist

def locatedCauchySubsequenceFromEventFlow :
    EventFlow → Option LocatedCauchySubsequenceUp
    -- BEDC touchpoint anchor: BHist BMark
    := fun ef =>
  List.casesOn ef none (fun M rest1 =>
    List.casesOn rest1 none (fun I rest2 =>
      List.casesOn rest2 none (fun D rest3 =>
        List.casesOn rest3 none (fun W rest4 =>
          List.casesOn rest4 none (fun R rest5 =>
            List.casesOn rest5 none (fun E rest6 =>
              List.casesOn rest6 none (fun H rest7 =>
                List.casesOn rest7 none (fun C rest8 =>
                  List.casesOn rest8 none (fun P rest9 =>
                    List.casesOn rest9 none (fun N rest10 =>
                      List.casesOn rest10
                        (some
                          (LocatedCauchySubsequenceUp.mk
                            (locatedCauchySubsequenceDecodeBHist M)
                            (locatedCauchySubsequenceDecodeBHist I)
                            (locatedCauchySubsequenceDecodeBHist D)
                            (locatedCauchySubsequenceDecodeBHist W)
                            (locatedCauchySubsequenceDecodeBHist R)
                            (locatedCauchySubsequenceDecodeBHist E)
                            (locatedCauchySubsequenceDecodeBHist H)
                            (locatedCauchySubsequenceDecodeBHist C)
                            (locatedCauchySubsequenceDecodeBHist P)
                            (locatedCauchySubsequenceDecodeBHist N)))
                        (fun _ _ => none)))))))))))

private theorem LocatedCauchySubsequenceUp_round_trip :
    ∀ x : LocatedCauchySubsequenceUp,
      locatedCauchySubsequenceFromEventFlow (locatedCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M I D W R E H C P N =>
      change
        some
          (LocatedCauchySubsequenceUp.mk
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist M))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist I))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist D))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist W))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist R))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist E))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist H))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist C))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist P))
            (locatedCauchySubsequenceDecodeBHist
              (locatedCauchySubsequenceEncodeBHist N))) =
          some (LocatedCauchySubsequenceUp.mk M I D W R E H C P N)
      rw [LocatedCauchySubsequenceUp_decode M, LocatedCauchySubsequenceUp_decode I,
        LocatedCauchySubsequenceUp_decode D, LocatedCauchySubsequenceUp_decode W,
        LocatedCauchySubsequenceUp_decode R, LocatedCauchySubsequenceUp_decode E,
        LocatedCauchySubsequenceUp_decode H, LocatedCauchySubsequenceUp_decode C,
        LocatedCauchySubsequenceUp_decode P, LocatedCauchySubsequenceUp_decode N]

private theorem LocatedCauchySubsequenceUp_toEventFlow_injective
    {x y : LocatedCauchySubsequenceUp} :
    locatedCauchySubsequenceToEventFlow x = locatedCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchySubsequenceFromEventFlow (locatedCauchySubsequenceToEventFlow x) =
        locatedCauchySubsequenceFromEventFlow (locatedCauchySubsequenceToEventFlow y) :=
    congrArg locatedCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchySubsequenceUp_round_trip x).symm
      (Eq.trans hread (LocatedCauchySubsequenceUp_round_trip y)))

instance locatedCauchySubsequenceBHistCarrier :
    BHistCarrier LocatedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchySubsequenceToEventFlow
  fromEventFlow := locatedCauchySubsequenceFromEventFlow

instance locatedCauchySubsequenceChapterTasteGate :
    ChapterTasteGate LocatedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchySubsequenceFromEventFlow (locatedCauchySubsequenceToEventFlow x) =
      some x
    exact LocatedCauchySubsequenceUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchySubsequenceUp_toEventFlow_injective heq)

theorem LocatedCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchySubsequenceDecodeBHist (locatedCauchySubsequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCauchySubsequenceUp) ∧
        Nonempty (ChapterTasteGate LocatedCauchySubsequenceUp) ∧
          locatedCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedCauchySubsequenceUp_decode,
      ⟨locatedCauchySubsequenceBHistCarrier⟩,
      ⟨locatedCauchySubsequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCauchySubsequenceUp

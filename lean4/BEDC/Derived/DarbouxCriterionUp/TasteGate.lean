import BEDC.Derived.DarbouxCriterionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def darbouxCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxCriterionEncodeBHist h

def darbouxCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxCriterionDecodeBHist tail)

private theorem DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxCriterionToEventFlow : DarbouxCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxCriterionUp.mk P L U G T R E H C Q N =>
      [darbouxCriterionEncodeBHist P,
        darbouxCriterionEncodeBHist L,
        darbouxCriterionEncodeBHist U,
        darbouxCriterionEncodeBHist G,
        darbouxCriterionEncodeBHist T,
        darbouxCriterionEncodeBHist R,
        darbouxCriterionEncodeBHist E,
        darbouxCriterionEncodeBHist H,
        darbouxCriterionEncodeBHist C,
        darbouxCriterionEncodeBHist Q,
        darbouxCriterionEncodeBHist N]

def darbouxCriterionFromEventFlow : EventFlow → Option DarbouxCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | P :: L :: U :: G :: T :: R :: E :: H :: C :: Q :: N :: [] =>
      some
        (DarbouxCriterionUp.mk
          (darbouxCriterionDecodeBHist P)
          (darbouxCriterionDecodeBHist L)
          (darbouxCriterionDecodeBHist U)
          (darbouxCriterionDecodeBHist G)
          (darbouxCriterionDecodeBHist T)
          (darbouxCriterionDecodeBHist R)
          (darbouxCriterionDecodeBHist E)
          (darbouxCriterionDecodeBHist H)
          (darbouxCriterionDecodeBHist C)
          (darbouxCriterionDecodeBHist Q)
          (darbouxCriterionDecodeBHist N))
  | _ => none

private theorem DarbouxCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxCriterionUp,
      darbouxCriterionFromEventFlow (darbouxCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P L U G T R E H C Q N =>
      change
        some
          (DarbouxCriterionUp.mk
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist P))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist L))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist U))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))) =
          some (DarbouxCriterionUp.mk P L U G T R E H C Q N)
      rw [DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode L,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode U,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode G,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode T,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode E,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode C,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode Q,
        DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DarbouxCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxCriterionUp} :
    darbouxCriterionToEventFlow x = darbouxCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxCriterionFromEventFlow (darbouxCriterionToEventFlow x) =
        darbouxCriterionFromEventFlow (darbouxCriterionToEventFlow y) :=
    congrArg darbouxCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DarbouxCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance darbouxCriterionBHistCarrier : BHistCarrier DarbouxCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxCriterionToEventFlow
  fromEventFlow := darbouxCriterionFromEventFlow

instance darbouxCriterionChapterTasteGate : ChapterTasteGate DarbouxCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxCriterionFromEventFlow (darbouxCriterionToEventFlow x) = some x
    exact DarbouxCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DarbouxCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxCriterionChapterTasteGate

private theorem DarbouxCriterionTasteGate_single_carrier_alignment_encode_injective
    {x y : BHist} :
    darbouxCriterionEncodeBHist x = darbouxCriterionEncodeBHist y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist x) =
        darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist y) :=
    congrArg darbouxCriterionDecodeBHist heq
  exact Eq.trans
    (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode x).symm
    (Eq.trans hdecode
      (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode y))

private theorem DarbouxCriterionTasteGate_single_carrier_alignment_raw_readback
    (P L U G T R E H C Q N : BHist) :
    some
        (DarbouxCriterionUp.mk
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist P))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist L))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist U))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))) =
      some (DarbouxCriterionUp.mk P L U G T R E H C Q N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    Eq.trans
      (congrArg
        (fun z => some
          (DarbouxCriterionUp.mk z
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist L))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist U))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
        (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode P))
      (Eq.trans
        (congrArg
          (fun z => some
            (DarbouxCriterionUp.mk P z
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist U))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
          (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode L))
        (Eq.trans
          (congrArg
            (fun z => some
              (DarbouxCriterionUp.mk P L z
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
            (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode U))
          (Eq.trans
            (congrArg
              (fun z => some
                (DarbouxCriterionUp.mk P L U z
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                  (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
              (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode G))
            (Eq.trans
              (congrArg
                (fun z => some
                  (DarbouxCriterionUp.mk P L U G z
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                    (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode T))
              (Eq.trans
                (congrArg
                  (fun z => some
                    (DarbouxCriterionUp.mk P L U G T z
                      (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
                      (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
                      (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                      (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                      (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                  (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode R))
                (Eq.trans
                  (congrArg
                    (fun z => some
                      (DarbouxCriterionUp.mk P L U G T R z
                        (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
                        (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                        (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                        (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                    (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode E))
                  (Eq.trans
                    (congrArg
                      (fun z => some
                        (DarbouxCriterionUp.mk P L U G T R E z
                          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
                          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                          (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                      (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode H))
                    (Eq.trans
                      (congrArg
                        (fun z => some
                          (DarbouxCriterionUp.mk P L U G T R E H z
                            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
                            (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                        (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode C))
                      (Eq.trans
                        (congrArg
                          (fun z => some
                            (DarbouxCriterionUp.mk P L U G T R E H C z
                              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))))
                          (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode Q))
                        (congrArg
                          (fun z => some (DarbouxCriterionUp.mk P L U G T R E H C Q z))
                          (DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode N)))))))))))

theorem DarbouxCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist h) = h) ∧
      (∀ P L U G T R E H C Q N : BHist,
        some
            (DarbouxCriterionUp.mk
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist P))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist L))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist U))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist G))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist T))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist R))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist E))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist H))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist C))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist Q))
              (darbouxCriterionDecodeBHist (darbouxCriterionEncodeBHist N))) =
          some (DarbouxCriterionUp.mk P L U G T R E H C Q N)) ∧
      (∀ x y : BHist,
        darbouxCriterionEncodeBHist x = darbouxCriterionEncodeBHist y → x = y) ∧
      darbouxCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DarbouxCriterionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DarbouxCriterionTasteGate_single_carrier_alignment_raw_readback
  constructor
  · intro x y heq
    exact DarbouxCriterionTasteGate_single_carrier_alignment_encode_injective heq
  · rfl

end BEDC.Derived.DarbouxCriterionUp

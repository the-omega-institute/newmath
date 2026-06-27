import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OgdenLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OgdenLemmaUp : Type where
  | mk (G W M D A E I Y H C R Q N : BHist) : OgdenLemmaUp
  deriving DecidableEq

def ogdenLemmaFields : OgdenLemmaUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OgdenLemmaUp.mk G W M D A E I Y H C R Q N =>
      [G, W, M, D, A, E, I, Y, H, C, R, Q, N]

def ogdenLemmaEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ogdenLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ogdenLemmaEncodeBHist h

def ogdenLemmaDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ogdenLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ogdenLemmaDecodeBHist tail)

theorem OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist :
    forall h : BHist, ogdenLemmaDecodeBHist (ogdenLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem OgdenLemmaTasteGate_single_carrier_alignment_mk_congr
    {G1 G2 W1 W2 M1 M2 D1 D2 A1 A2 E1 E2 I1 I2 Y1 Y2 H1 H2 C1 C2 R1 R2 Q1 Q2
      N1 N2 : BHist}
    (hG : G1 = G2) (hW : W1 = W2) (hM : M1 = M2) (hD : D1 = D2)
    (hA : A1 = A2) (hE : E1 = E2) (hI : I1 = I2) (hY : Y1 = Y2)
    (hH : H1 = H2) (hC : C1 = C2) (hR : R1 = R2) (hQ : Q1 = Q2)
    (hN : N1 = N2) :
    OgdenLemmaUp.mk G1 W1 M1 D1 A1 E1 I1 Y1 H1 C1 R1 Q1 N1 =
      OgdenLemmaUp.mk G2 W2 M2 D2 A2 E2 I2 Y2 H2 C2 R2 Q2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hG
  cases hW
  cases hM
  cases hD
  cases hA
  cases hE
  cases hI
  cases hY
  cases hH
  cases hC
  cases hR
  cases hQ
  cases hN
  rfl

def ogdenLemmaToEventFlow : OgdenLemmaUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OgdenLemmaUp.mk G W M D A E I Y H C R Q N =>
      [ogdenLemmaEncodeBHist G, ogdenLemmaEncodeBHist W, ogdenLemmaEncodeBHist M,
        ogdenLemmaEncodeBHist D, ogdenLemmaEncodeBHist A, ogdenLemmaEncodeBHist E,
        ogdenLemmaEncodeBHist I, ogdenLemmaEncodeBHist Y, ogdenLemmaEncodeBHist H,
        ogdenLemmaEncodeBHist C, ogdenLemmaEncodeBHist R, ogdenLemmaEncodeBHist Q,
        ogdenLemmaEncodeBHist N]

private def ogdenLemmaEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ogdenLemmaEventAtDefault index rest

def ogdenLemmaFromEventFlow (ef : EventFlow) : Option OgdenLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OgdenLemmaUp.mk
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 0 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 1 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 2 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 3 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 4 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 5 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 6 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 7 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 8 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 9 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 10 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 11 ef))
      (ogdenLemmaDecodeBHist (ogdenLemmaEventAtDefault 12 ef)))

theorem OgdenLemmaTasteGate_single_carrier_alignment_round_trip :
    forall x : OgdenLemmaUp,
      ogdenLemmaFromEventFlow (ogdenLemmaToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | OgdenLemmaUp.mk G W M D A E I Y H C R Q N =>
      congrArg some
        (OgdenLemmaTasteGate_single_carrier_alignment_mk_congr
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist G)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist W)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist M)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist D)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist A)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist E)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist I)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist Y)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist H)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist C)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist R)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist Q)
          (OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist N))

theorem OgdenLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OgdenLemmaUp} :
    ogdenLemmaToEventFlow x = ogdenLemmaToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ogdenLemmaFromEventFlow (ogdenLemmaToEventFlow x) =
        ogdenLemmaFromEventFlow (ogdenLemmaToEventFlow y) :=
    congrArg ogdenLemmaFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (OgdenLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OgdenLemmaTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance ogdenLemmaBHistCarrier : BHistCarrier OgdenLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ogdenLemmaToEventFlow
  fromEventFlow := ogdenLemmaFromEventFlow

instance ogdenLemmaChapterTasteGate : ChapterTasteGate OgdenLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ogdenLemmaFromEventFlow (ogdenLemmaToEventFlow x) = some x
    exact OgdenLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OgdenLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate OgdenLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ogdenLemmaChapterTasteGate

theorem OgdenLemmaTasteGate_single_carrier_alignment :
    Nonempty OgdenLemmaUp ∧
      (∀ h : BHist,
        ogdenLemmaDecodeBHist (ogdenLemmaEncodeBHist h) = h ∧
          ogdenLemmaEncodeBHist (BHist.e0 h) =
            BMark.b0 :: ogdenLemmaEncodeBHist h) ∧
      (∀ x : OgdenLemmaUp, ogdenLemmaFromEventFlow (ogdenLemmaToEventFlow x) = some x) ∧
      (∀ x y : OgdenLemmaUp, ogdenLemmaToEventFlow x = ogdenLemmaToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      Nonempty.intro
        (OgdenLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty)
  · constructor
    · intro h
      exact
        ⟨OgdenLemmaTasteGate_single_carrier_alignment_decode_encode_bhist h, rfl⟩
    · constructor
      · exact OgdenLemmaTasteGate_single_carrier_alignment_round_trip
      · intro x y heq
        exact OgdenLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq

end BEDC.Derived.OgdenLemmaUp

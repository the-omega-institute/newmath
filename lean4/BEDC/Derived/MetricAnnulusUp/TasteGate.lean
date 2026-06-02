import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricAnnulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricAnnulusUp : Type where
  | mk (M c r0 r1 O B H C P N : BHist) : MetricAnnulusUp
  deriving DecidableEq

private def metricAnnulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricAnnulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricAnnulusEncodeBHist h

private def metricAnnulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricAnnulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricAnnulusDecodeBHist tail)

private theorem metricAnnulus_decode_encode_bhist :
    forall h : BHist, metricAnnulusDecodeBHist (metricAnnulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def metricAnnulusFields : MetricAnnulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricAnnulusUp.mk M c r0 r1 O B H C P N => [M, c, r0, r1, O, B, H, C, P, N]

private def metricAnnulusToEventFlow : MetricAnnulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | K => (metricAnnulusFields K).map metricAnnulusEncodeBHist

private def metricAnnulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricAnnulusEventAtDefault index rest

private def metricAnnulusFromEventFlow (ef : EventFlow) : Option MetricAnnulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricAnnulusUp.mk
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 0 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 1 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 2 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 3 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 4 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 5 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 6 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 7 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 8 ef))
      (metricAnnulusDecodeBHist (metricAnnulusEventAtDefault 9 ef)))

private theorem metricAnnulus_round_trip :
    forall K : MetricAnnulusUp,
      metricAnnulusFromEventFlow (metricAnnulusToEventFlow K) = some K := by
  -- BEDC touchpoint anchor: BHist BMark
  intro K
  cases K with
  | mk M c r0 r1 O B H C P N =>
      change
        some
          (MetricAnnulusUp.mk
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist M))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist c))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist r0))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist r1))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist O))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist B))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist H))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist C))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist P))
            (metricAnnulusDecodeBHist (metricAnnulusEncodeBHist N))) =
          some (MetricAnnulusUp.mk M c r0 r1 O B H C P N)
      rw [metricAnnulus_decode_encode_bhist M,
        metricAnnulus_decode_encode_bhist c,
        metricAnnulus_decode_encode_bhist r0,
        metricAnnulus_decode_encode_bhist r1,
        metricAnnulus_decode_encode_bhist O,
        metricAnnulus_decode_encode_bhist B,
        metricAnnulus_decode_encode_bhist H,
        metricAnnulus_decode_encode_bhist C,
        metricAnnulus_decode_encode_bhist P,
        metricAnnulus_decode_encode_bhist N]

private theorem metricAnnulusToEventFlow_injective {K L : MetricAnnulusUp} :
    metricAnnulusToEventFlow K = metricAnnulusToEventFlow L -> K = L := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricAnnulusFromEventFlow (metricAnnulusToEventFlow K) =
        metricAnnulusFromEventFlow (metricAnnulusToEventFlow L) :=
    congrArg metricAnnulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricAnnulus_round_trip K).symm
      (Eq.trans hread (metricAnnulus_round_trip L)))

instance metricAnnulusBHistCarrier : BHistCarrier MetricAnnulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricAnnulusToEventFlow
  fromEventFlow := metricAnnulusFromEventFlow

instance metricAnnulusChapterTasteGate : ChapterTasteGate MetricAnnulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro K
    change metricAnnulusFromEventFlow (metricAnnulusToEventFlow K) = some K
    exact metricAnnulus_round_trip K
  layer_separation := by
    intro K L hKL heq
    exact hKL (metricAnnulusToEventFlow_injective heq)

def MetricAnnulusCarrierRows (K : MetricAnnulusUp) : Prop :=
  match K with
  | MetricAnnulusUp.mk M c r0 r1 O B H C P N =>
      hsame M M /\ hsame c c /\ hsame r0 r0 /\ hsame r1 r1 /\
        hsame O O /\ hsame B B /\ hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def MetricAnnulusBoundaryRowsUse (K : MetricAnnulusUp) (route : BHist) : Prop :=
  match K with
  | MetricAnnulusUp.mk M c r0 r1 O B H C P N =>
      hsame route BHist.Empty /\ Cont M route M /\ Cont c route c /\
        hsame r0 r0 /\ hsame r1 r1 /\ hsame O O /\ hsame B B /\
          hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def MetricAnnulusNameCertSurface (K : MetricAnnulusUp) : Prop :=
  match K with
  | MetricAnnulusUp.mk _M _c _r0 _r1 _O _B _H _C _P N =>
      SemanticNameCert
        (fun row : BHist => hsame row N)
        (fun row : BHist => hsame row N /\ MetricAnnulusCarrierRows K)
        (fun row : BHist => hsame row N /\
          MetricAnnulusBoundaryRowsUse K BHist.Empty)
        hsame /\
      Nonempty (ChapterTasteGate MetricAnnulusUp)

theorem MetricAnnulusCarrier_namecert_obligations {K : MetricAnnulusUp} :
    MetricAnnulusCarrierRows K /\
      MetricAnnulusBoundaryRowsUse K BHist.Empty /\
      MetricAnnulusNameCertSurface K := by
  -- BEDC touchpoint anchor: BHist hsame Cont NameCert SemanticNameCert ChapterTasteGate
  cases K with
  | mk M c r0 r1 O B H C P N =>
      constructor
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · constructor
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · constructor
          · exact
              { core := {
                  carrier_inhabited := Exists.intro N rfl
                  equiv_refl := by
                    intro row _source
                    exact hsame_refl row
                  equiv_symm := by
                    intro row row' same
                    exact hsame_symm same
                  equiv_trans := by
                    intro row row' row'' sameLeft sameRight
                    exact hsame_trans sameLeft sameRight
                  carrier_respects_equiv := by
                    intro row row' same source
                    exact hsame_trans (hsame_symm same) source
                }
                pattern_sound := by
                  intro row source
                  exact
                    ⟨source, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
                ledger_sound := by
                  intro row source
                  exact
                    ⟨source,
                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
              }
          · exact Nonempty.intro metricAnnulusChapterTasteGate

end BEDC.Derived.MetricAnnulusUp

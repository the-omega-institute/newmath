import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MontelTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MontelTheoremUp : Type where
  | mk
      (K L E U Q G R D Z H C P N : BHist) :
      MontelTheoremUp
  deriving DecidableEq

def montelTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: montelTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: montelTheoremEncodeBHist h

def montelTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (montelTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (montelTheoremDecodeBHist tail)

private theorem MontelTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, montelTheoremDecodeBHist (montelTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem montelTheoremMk_congr
    {K K' L L' E E' U U' Q Q' G G' R R' D D' Z Z' H H' C C' P P' N N' : BHist}
    (hK : K = K') (hL : L = L') (hE : E = E') (hU : U = U') (hQ : Q = Q')
    (hG : G = G') (hR : R = R') (hD : D = D') (hZ : Z = Z') (hH : H = H')
    (hC : C = C') (hP : P = P') (hN : N = N') :
    MontelTheoremUp.mk K L E U Q G R D Z H C P N =
      MontelTheoremUp.mk K' L' E' U' Q' G' R' D' Z' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hL
  cases hE
  cases hU
  cases hQ
  cases hG
  cases hR
  cases hD
  cases hZ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def montelTheoremToEventFlow : MontelTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MontelTheoremUp.mk K L E U Q G R D Z H C P N =>
      [montelTheoremEncodeBHist K,
        montelTheoremEncodeBHist L,
        montelTheoremEncodeBHist E,
        montelTheoremEncodeBHist U,
        montelTheoremEncodeBHist Q,
        montelTheoremEncodeBHist G,
        montelTheoremEncodeBHist R,
        montelTheoremEncodeBHist D,
        montelTheoremEncodeBHist Z,
        montelTheoremEncodeBHist H,
        montelTheoremEncodeBHist C,
        montelTheoremEncodeBHist P,
        montelTheoremEncodeBHist N]

private def montelTheoremFromEventFlowTail
    (K L E U Q G R D Z H C P : RawEvent) :
    EventFlow → Option MontelTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | N :: [] =>
      some
        (MontelTheoremUp.mk
          (montelTheoremDecodeBHist K)
          (montelTheoremDecodeBHist L)
          (montelTheoremDecodeBHist E)
          (montelTheoremDecodeBHist U)
          (montelTheoremDecodeBHist Q)
          (montelTheoremDecodeBHist G)
          (montelTheoremDecodeBHist R)
          (montelTheoremDecodeBHist D)
          (montelTheoremDecodeBHist Z)
          (montelTheoremDecodeBHist H)
          (montelTheoremDecodeBHist C)
          (montelTheoremDecodeBHist P)
          (montelTheoremDecodeBHist N))
  | [] => none
  | _ :: _ :: _ => none

private def montelTheoremFromEventFlowAfterK
    (K : RawEvent) :
    EventFlow → Option MontelTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: E :: U :: Q :: G :: R :: D :: Z :: H :: C :: P :: tail =>
      montelTheoremFromEventFlowTail K L E U Q G R D Z H C P tail
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none

def montelTheoremFromEventFlow : EventFlow → Option MontelTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: tail => montelTheoremFromEventFlowAfterK K tail
  | [] => none

private theorem MontelTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MontelTheoremUp,
      montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L E U Q G R D Z H C P N =>
      change
        some
          (MontelTheoremUp.mk
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist K))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist L))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist E))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist U))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist Q))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist G))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist R))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist D))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist Z))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist H))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist C))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist P))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist N))) =
          some (MontelTheoremUp.mk K L E U Q G R D Z H C P N)
      exact
        congrArg some
          (montelTheoremMk_congr
            (MontelTheoremTasteGate_single_carrier_alignment_decode K)
            (MontelTheoremTasteGate_single_carrier_alignment_decode L)
            (MontelTheoremTasteGate_single_carrier_alignment_decode E)
            (MontelTheoremTasteGate_single_carrier_alignment_decode U)
            (MontelTheoremTasteGate_single_carrier_alignment_decode Q)
            (MontelTheoremTasteGate_single_carrier_alignment_decode G)
            (MontelTheoremTasteGate_single_carrier_alignment_decode R)
            (MontelTheoremTasteGate_single_carrier_alignment_decode D)
            (MontelTheoremTasteGate_single_carrier_alignment_decode Z)
            (MontelTheoremTasteGate_single_carrier_alignment_decode H)
            (MontelTheoremTasteGate_single_carrier_alignment_decode C)
            (MontelTheoremTasteGate_single_carrier_alignment_decode P)
            (MontelTheoremTasteGate_single_carrier_alignment_decode N))

private theorem MontelTheoremToEventFlow_injective {x y : MontelTheoremUp} :
    montelTheoremToEventFlow x = montelTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      montelTheoremFromEventFlow (montelTheoremToEventFlow x) =
        montelTheoremFromEventFlow (montelTheoremToEventFlow y) :=
    congrArg montelTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MontelTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MontelTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance montelTheoremBHistCarrier : BHistCarrier MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := montelTheoremToEventFlow
  fromEventFlow := montelTheoremFromEventFlow

instance montelTheoremChapterTasteGate : ChapterTasteGate MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x
    exact MontelTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MontelTheoremToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MontelTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  montelTheoremChapterTasteGate

theorem MontelTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, montelTheoremDecodeBHist (montelTheoremEncodeBHist h) = h) ∧
      (∀ x : MontelTheoremUp,
        montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x) ∧
      (∀ x y : MontelTheoremUp,
        montelTheoremToEventFlow x = montelTheoremToEventFlow y → x = y) ∧
      montelTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MontelTheoremTasteGate_single_carrier_alignment_decode,
      MontelTheoremTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => MontelTheoremToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.MontelTheoremUp

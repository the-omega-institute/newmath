import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMetastabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMetastabilityUp : Type where
  | mk (p g W D Q E H C P N : BHist) : CauchyMetastabilityUp
  deriving DecidableEq

def cauchyMetastabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMetastabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMetastabilityEncodeBHist h

def cauchyMetastabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMetastabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMetastabilityDecodeBHist tail)

private theorem CauchyMetastabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyMetastabilityDecodeBHist (cauchyMetastabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMetastabilityFields : CauchyMetastabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMetastabilityUp.mk p g W D Q E H C P N =>
      [p, g, W, D, Q, E, H, C, P, N]

def cauchyMetastabilityToEventFlow : CauchyMetastabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMetastabilityFields x).map cauchyMetastabilityEncodeBHist

def cauchyMetastabilityFromEventFlow :
    EventFlow → Option CauchyMetastabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | p :: restPRequest =>
      match restPRequest with
      | g :: restG =>
          match restG with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | Q :: restQ =>
                      match restQ with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchyMetastabilityUp.mk
                                                  (cauchyMetastabilityDecodeBHist p)
                                                  (cauchyMetastabilityDecodeBHist g)
                                                  (cauchyMetastabilityDecodeBHist W)
                                                  (cauchyMetastabilityDecodeBHist D)
                                                  (cauchyMetastabilityDecodeBHist Q)
                                                  (cauchyMetastabilityDecodeBHist E)
                                                  (cauchyMetastabilityDecodeBHist H)
                                                  (cauchyMetastabilityDecodeBHist C)
                                                  (cauchyMetastabilityDecodeBHist P)
                                                  (cauchyMetastabilityDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyMetastability_mk_congr
    {p p' g g' W W' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hp : p' = p) (hg : g' = g) (hW : W' = W) (hD : D' = D)
    (hQ : Q' = Q) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyMetastabilityUp.mk p' g' W' D' Q' E' H' C' P' N' =
      CauchyMetastabilityUp.mk p g W D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hp
  cases hg
  cases hW
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyMetastabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyMetastabilityUp,
      cauchyMetastabilityFromEventFlow
        (cauchyMetastabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p g W D Q E H C P N =>
      exact
        congrArg some
          (cauchyMetastability_mk_congr
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode p)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode g)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode W)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode D)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode Q)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode E)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode H)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode C)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode P)
            (CauchyMetastabilityTasteGate_single_carrier_alignment_decode N))

private theorem CauchyMetastabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMetastabilityUp} :
    cauchyMetastabilityToEventFlow x =
      cauchyMetastabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMetastabilityFromEventFlow (cauchyMetastabilityToEventFlow x) =
        cauchyMetastabilityFromEventFlow (cauchyMetastabilityToEventFlow y) :=
    congrArg cauchyMetastabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyMetastabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyMetastabilityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyMetastabilityBHistCarrier : BHistCarrier CauchyMetastabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMetastabilityToEventFlow
  fromEventFlow := cauchyMetastabilityFromEventFlow

instance cauchyMetastabilityChapterTasteGate :
    ChapterTasteGate CauchyMetastabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyMetastabilityFromEventFlow
        (cauchyMetastabilityToEventFlow x) = some x
    exact CauchyMetastabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyMetastabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyMetastabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyMetastabilityChapterTasteGate

theorem CauchyMetastabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyMetastabilityDecodeBHist (cauchyMetastabilityEncodeBHist h) = h) ∧
      (∀ x : CauchyMetastabilityUp,
        cauchyMetastabilityFromEventFlow
          (cauchyMetastabilityToEventFlow x) = some x) ∧
        (∀ x y : CauchyMetastabilityUp,
          cauchyMetastabilityToEventFlow x =
            cauchyMetastabilityToEventFlow y → x = y) ∧
          cauchyMetastabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyMetastabilityTasteGate_single_carrier_alignment_decode,
      CauchyMetastabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyMetastabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyMetastabilityUp

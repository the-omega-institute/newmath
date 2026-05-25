import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusNormalFormUp : Type where
  | mk (p mu nu tau W Q E H C P N : BHist) : CauchyModulusNormalFormUp
  deriving DecidableEq

def cauchyModulusNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusNormalFormEncodeBHist h

def cauchyModulusNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusNormalFormDecodeBHist tail)

private theorem cauchyModulusNormalForm_decode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusNormalFormDecodeBHist
        (cauchyModulusNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyModulusNormalForm_mk_congr
    {p p' mu mu' nu nu' tau tau' W W' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hp : p' = p) (hmu : mu' = mu) (hnu : nu' = nu) (htau : tau' = tau)
    (hW : W' = W) (hQ : Q' = Q) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyModulusNormalFormUp.mk p' mu' nu' tau' W' Q' E' H' C' P' N' =
      CauchyModulusNormalFormUp.mk p mu nu tau W Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hp
  cases hmu
  cases hnu
  cases htau
  cases hW
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyModulusNormalFormFields :
    CauchyModulusNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusNormalFormUp.mk p mu nu tau W Q E H C P N =>
      [p, mu, nu, tau, W, Q, E, H, C, P, N]

def cauchyModulusNormalFormToEventFlow :
    CauchyModulusNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusNormalFormFields x).map
      cauchyModulusNormalFormEncodeBHist

private def cauchyModulusNormalFormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | _, [] => []
  | 0, row :: _ => row
  | n + 1, _ :: rows => cauchyModulusNormalFormEventAtDefault n rows

def cauchyModulusNormalFormFromEventFlow
    (ef : EventFlow) : Option CauchyModulusNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef.length with
  | 11 =>
      some
        (CauchyModulusNormalFormUp.mk
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 0 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 1 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 2 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 3 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 4 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 5 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 6 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 7 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 8 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 9 ef))
          (cauchyModulusNormalFormDecodeBHist
            (cauchyModulusNormalFormEventAtDefault 10 ef)))
  | _ => none

private theorem cauchyModulusNormalForm_round_trip :
    ∀ x : CauchyModulusNormalFormUp,
      cauchyModulusNormalFormFromEventFlow
        (cauchyModulusNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p mu nu tau W Q E H C P N =>
      change
        some
          (CauchyModulusNormalFormUp.mk
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist p))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist mu))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist nu))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist tau))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist W))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist Q))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist E))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist H))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist C))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist P))
            (cauchyModulusNormalFormDecodeBHist
              (cauchyModulusNormalFormEncodeBHist N))) =
          some (CauchyModulusNormalFormUp.mk p mu nu tau W Q E H C P N)
      exact
        congrArg some
          (cauchyModulusNormalForm_mk_congr
            (cauchyModulusNormalForm_decode_encode_bhist p)
            (cauchyModulusNormalForm_decode_encode_bhist mu)
            (cauchyModulusNormalForm_decode_encode_bhist nu)
            (cauchyModulusNormalForm_decode_encode_bhist tau)
            (cauchyModulusNormalForm_decode_encode_bhist W)
            (cauchyModulusNormalForm_decode_encode_bhist Q)
            (cauchyModulusNormalForm_decode_encode_bhist E)
            (cauchyModulusNormalForm_decode_encode_bhist H)
            (cauchyModulusNormalForm_decode_encode_bhist C)
            (cauchyModulusNormalForm_decode_encode_bhist P)
            (cauchyModulusNormalForm_decode_encode_bhist N))

private theorem cauchyModulusNormalFormToEventFlow_injective
    {x y : CauchyModulusNormalFormUp} :
    cauchyModulusNormalFormToEventFlow x =
      cauchyModulusNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusNormalFormFromEventFlow
          (cauchyModulusNormalFormToEventFlow x) =
        cauchyModulusNormalFormFromEventFlow
          (cauchyModulusNormalFormToEventFlow y) :=
    congrArg cauchyModulusNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusNormalForm_round_trip x).symm
      (Eq.trans hread (cauchyModulusNormalForm_round_trip y)))

instance cauchyModulusNormalFormBHistCarrier :
    BHistCarrier CauchyModulusNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusNormalFormToEventFlow
  fromEventFlow := cauchyModulusNormalFormFromEventFlow

instance cauchyModulusNormalFormChapterTasteGate :
    ChapterTasteGate CauchyModulusNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusNormalFormFromEventFlow
        (cauchyModulusNormalFormToEventFlow x) = some x
    exact cauchyModulusNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusNormalFormToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusNormalFormChapterTasteGate

theorem CauchyModulusNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusNormalFormDecodeBHist
        (cauchyModulusNormalFormEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyModulusNormalFormUp) ∧
        Nonempty (ChapterTasteGate CauchyModulusNormalFormUp) ∧
          cauchyModulusNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyModulusNormalForm_decode_encode_bhist
  · constructor
    · exact ⟨cauchyModulusNormalFormBHistCarrier⟩
    · constructor
      · exact ⟨cauchyModulusNormalFormChapterTasteGate⟩
      · rfl

end BEDC.Derived.CauchyModulusNormalFormUp

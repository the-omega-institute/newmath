import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceUp : Type where
  | mk (F W Q R T H C P N : BHist) : UniformConvergenceUp
  deriving DecidableEq

def uniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceEncodeBHist h

def uniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceDecodeBHist tail)

private theorem uniformConvergence_decode_encode_bhist :
    ∀ h : BHist, uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem uniformConvergence_mk_congr
    {F F' W W' Q Q' R R' T T' H H' C C' P P' N N' : BHist}
    (hF : F' = F) (hW : W' = W) (hQ : Q' = Q) (hR : R' = R)
    (hT : T' = T) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    UniformConvergenceUp.mk F' W' Q' R' T' H' C' P' N' =
      UniformConvergenceUp.mk F W Q R T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hW
  cases hQ
  cases hR
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def uniformConvergenceFields : UniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceUp.mk F W Q R T H C P N => [F, W, Q, R, T, H, C, P, N]

def uniformConvergenceToEventFlow : UniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformConvergenceFields x).map uniformConvergenceEncodeBHist

def uniformConvergenceFromEventFlow : EventFlow → Option UniformConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _F :: [] => none
  | _F :: _W :: [] => none
  | _F :: _W :: _Q :: [] => none
  | _F :: _W :: _Q :: _R :: [] => none
  | _F :: _W :: _Q :: _R :: _T :: [] => none
  | _F :: _W :: _Q :: _R :: _T :: _H :: [] => none
  | _F :: _W :: _Q :: _R :: _T :: _H :: _C :: [] => none
  | _F :: _W :: _Q :: _R :: _T :: _H :: _C :: _P :: [] => none
  | F :: W :: Q :: R :: T :: H :: C :: P :: N :: [] =>
      some
        (UniformConvergenceUp.mk
          (uniformConvergenceDecodeBHist F)
          (uniformConvergenceDecodeBHist W)
          (uniformConvergenceDecodeBHist Q)
          (uniformConvergenceDecodeBHist R)
          (uniformConvergenceDecodeBHist T)
          (uniformConvergenceDecodeBHist H)
          (uniformConvergenceDecodeBHist C)
          (uniformConvergenceDecodeBHist P)
          (uniformConvergenceDecodeBHist N))
  | _F :: _W :: _Q :: _R :: _T :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem uniformConvergence_round_trip :
    ∀ x : UniformConvergenceUp,
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W Q R T H C P N =>
      exact
        congrArg some
          (uniformConvergence_mk_congr
            (uniformConvergence_decode_encode_bhist F)
            (uniformConvergence_decode_encode_bhist W)
            (uniformConvergence_decode_encode_bhist Q)
            (uniformConvergence_decode_encode_bhist R)
            (uniformConvergence_decode_encode_bhist T)
            (uniformConvergence_decode_encode_bhist H)
            (uniformConvergence_decode_encode_bhist C)
            (uniformConvergence_decode_encode_bhist P)
            (uniformConvergence_decode_encode_bhist N))

private theorem uniformConvergenceToEventFlow_injective {x y : UniformConvergenceUp} :
    uniformConvergenceToEventFlow x = uniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) =
        uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow y) :=
    congrArg uniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformConvergence_round_trip x).symm
      (Eq.trans hread (uniformConvergence_round_trip y)))

instance uniformConvergenceBHistCarrier : BHistCarrier UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceToEventFlow
  fromEventFlow := uniformConvergenceFromEventFlow

instance uniformConvergenceChapterTasteGate : ChapterTasteGate UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x
    exact uniformConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformConvergenceChapterTasteGate

theorem UniformConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier UniformConvergenceUp) ∧
      Nonempty (ChapterTasteGate UniformConvergenceUp) ∧
      (∀ h : BHist,
        uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h) ∧
      (∀ x : UniformConvergenceUp,
        uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x) ∧
      (∀ x y : UniformConvergenceUp,
        uniformConvergenceToEventFlow x = uniformConvergenceToEventFlow y → x = y) ∧
      uniformConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨uniformConvergenceBHistCarrier⟩,
      ⟨uniformConvergenceChapterTasteGate⟩,
      uniformConvergence_decode_encode_bhist,
      uniformConvergence_round_trip,
      (fun _ _ heq => uniformConvergenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformConvergenceUp.TasteGate

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceSpaceUp : Type where
  | mk (D F W T R E H C P N : BHist) : UniformConvergenceSpaceUp
  deriving DecidableEq

def uniformConvergenceSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceSpaceEncodeBHist h

def uniformConvergenceSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceSpaceDecodeBHist tail)

private theorem uniformConvergenceSpace_decode_encode :
    ∀ h : BHist,
      uniformConvergenceSpaceDecodeBHist (uniformConvergenceSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem uniformConvergenceSpace_mk_congr
    {D D' F F' W W' T T' R R' E E' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hF : F' = F) (hW : W' = W) (hT : T' = T) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    UniformConvergenceSpaceUp.mk D' F' W' T' R' E' H' C' P' N' =
      UniformConvergenceSpaceUp.mk D F W T R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hF
  cases hW
  cases hT
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def uniformConvergenceSpaceFields : UniformConvergenceSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceSpaceUp.mk D F W T R E H C P N => [D, F, W, T, R, E, H, C, P, N]

def uniformConvergenceSpaceToEventFlow : UniformConvergenceSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformConvergenceSpaceFields x).map uniformConvergenceSpaceEncodeBHist

def uniformConvergenceSpaceFromEventFlow : EventFlow → Option UniformConvergenceSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _D :: [] => none
  | _D :: _F :: [] => none
  | _D :: _F :: _W :: [] => none
  | _D :: _F :: _W :: _T :: [] => none
  | _D :: _F :: _W :: _T :: _R :: [] => none
  | _D :: _F :: _W :: _T :: _R :: _E :: [] => none
  | _D :: _F :: _W :: _T :: _R :: _E :: _H :: [] => none
  | _D :: _F :: _W :: _T :: _R :: _E :: _H :: _C :: [] => none
  | _D :: _F :: _W :: _T :: _R :: _E :: _H :: _C :: _P :: [] => none
  | D :: F :: W :: T :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (UniformConvergenceSpaceUp.mk
          (uniformConvergenceSpaceDecodeBHist D)
          (uniformConvergenceSpaceDecodeBHist F)
          (uniformConvergenceSpaceDecodeBHist W)
          (uniformConvergenceSpaceDecodeBHist T)
          (uniformConvergenceSpaceDecodeBHist R)
          (uniformConvergenceSpaceDecodeBHist E)
          (uniformConvergenceSpaceDecodeBHist H)
          (uniformConvergenceSpaceDecodeBHist C)
          (uniformConvergenceSpaceDecodeBHist P)
          (uniformConvergenceSpaceDecodeBHist N))
  | _D :: _F :: _W :: _T :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem uniformConvergenceSpace_round_trip :
    ∀ x : UniformConvergenceSpaceUp,
      uniformConvergenceSpaceFromEventFlow (uniformConvergenceSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D F W T R E H C P N =>
      exact uniformConvergenceSpace_round_trip_mk
where
  uniformConvergenceSpace_round_trip_mk {D F W T R E H C P N : BHist} :
      uniformConvergenceSpaceFromEventFlow
          (uniformConvergenceSpaceToEventFlow
            (UniformConvergenceSpaceUp.mk D F W T R E H C P N)) =
        some (UniformConvergenceSpaceUp.mk D F W T R E H C P N) := by
    -- BEDC touchpoint anchor: BHist BMark
    exact
      congrArg some
        (uniformConvergenceSpace_mk_congr
          (uniformConvergenceSpace_decode_encode D)
          (uniformConvergenceSpace_decode_encode F)
          (uniformConvergenceSpace_decode_encode W)
          (uniformConvergenceSpace_decode_encode T)
          (uniformConvergenceSpace_decode_encode R)
          (uniformConvergenceSpace_decode_encode E)
          (uniformConvergenceSpace_decode_encode H)
          (uniformConvergenceSpace_decode_encode C)
          (uniformConvergenceSpace_decode_encode P)
          (uniformConvergenceSpace_decode_encode N))

private theorem uniformConvergenceSpaceToEventFlow_injective
    {x y : UniformConvergenceSpaceUp} :
    uniformConvergenceSpaceToEventFlow x = uniformConvergenceSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceSpaceFromEventFlow (uniformConvergenceSpaceToEventFlow x) =
        uniformConvergenceSpaceFromEventFlow (uniformConvergenceSpaceToEventFlow y) :=
    congrArg uniformConvergenceSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformConvergenceSpace_round_trip x).symm
      (Eq.trans hread (uniformConvergenceSpace_round_trip y)))

private theorem uniformConvergenceSpace_field_faithful :
    ∀ x y : UniformConvergenceSpaceUp,
      uniformConvergenceSpaceFields x = uniformConvergenceSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D F W T R E H C P N =>
      cases y with
      | mk D' F' W' T' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance uniformConvergenceSpaceBHistCarrier : BHistCarrier UniformConvergenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceSpaceToEventFlow
  fromEventFlow := uniformConvergenceSpaceFromEventFlow

instance uniformConvergenceSpaceChapterTasteGate :
    ChapterTasteGate UniformConvergenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformConvergenceSpaceFromEventFlow (uniformConvergenceSpaceToEventFlow x) = some x
    exact uniformConvergenceSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformConvergenceSpaceToEventFlow_injective heq)

instance uniformConvergenceSpaceFieldFaithful :
    FieldFaithful UniformConvergenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformConvergenceSpaceFields
  field_faithful := uniformConvergenceSpace_field_faithful

def taste_gate : ChapterTasteGate UniformConvergenceSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformConvergenceSpaceChapterTasteGate

theorem UniformConvergenceSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformConvergenceSpaceDecodeBHist (uniformConvergenceSpaceEncodeBHist h) = h) ∧
      (∀ x : UniformConvergenceSpaceUp,
        uniformConvergenceSpaceFromEventFlow (uniformConvergenceSpaceToEventFlow x) = some x) ∧
        (∀ x y : UniformConvergenceSpaceUp,
          uniformConvergenceSpaceToEventFlow x = uniformConvergenceSpaceToEventFlow y →
            x = y) ∧
          uniformConvergenceSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨uniformConvergenceSpace_decode_encode, uniformConvergenceSpace_round_trip,
      (fun _ _ heq => uniformConvergenceSpaceToEventFlow_injective heq), rfl⟩

end BEDC.Derived.UniformConvergenceSpaceUp

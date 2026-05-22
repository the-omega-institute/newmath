import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMinMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealMinMaxUp : Type where
  | mk
      (X Y RX RY SX SY D E C O L U H T P N : BHist) :
      RealMinMaxUp
  deriving DecidableEq

def realMinMaxEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realMinMaxEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realMinMaxEncodeBHist h

def realMinMaxDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realMinMaxDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realMinMaxDecodeBHist tail)

private theorem RealMinMaxTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realMinMaxDecodeBHist (realMinMaxEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realMinMaxFields : RealMinMaxUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N =>
      [X, Y, RX, RY, SX, SY, D, E, C, O, L, U, H, T, P, N]

private theorem realMinMax_mk_congr
    {X₁ X₂ Y₁ Y₂ RX₁ RX₂ RY₁ RY₂ SX₁ SX₂ SY₁ SY₂ D₁ D₂ E₁ E₂ C₁ C₂ O₁ O₂
      L₁ L₂ U₁ U₂ H₁ H₂ T₁ T₂ P₁ P₂ N₁ N₂ : BHist} :
    X₁ = X₂ → Y₁ = Y₂ → RX₁ = RX₂ → RY₁ = RY₂ → SX₁ = SX₂ → SY₁ = SY₂ →
      D₁ = D₂ → E₁ = E₂ → C₁ = C₂ → O₁ = O₂ → L₁ = L₂ → U₁ = U₂ →
        H₁ = H₂ → T₁ = T₂ → P₁ = P₂ → N₁ = N₂ →
          RealMinMaxUp.mk X₁ Y₁ RX₁ RY₁ SX₁ SY₁ D₁ E₁ C₁ O₁ L₁ U₁ H₁ T₁ P₁ N₁ =
            RealMinMaxUp.mk X₂ Y₂ RX₂ RY₂ SX₂ SY₂ D₂ E₂ C₂ O₂ L₂ U₂ H₂ T₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hX hY hRX hRY hSX hSY hD hE hC hO hL hU hH hT hP hN
  cases hX
  cases hY
  cases hRX
  cases hRY
  cases hSX
  cases hSY
  cases hD
  cases hE
  cases hC
  cases hO
  cases hL
  cases hU
  cases hH
  cases hT
  cases hP
  cases hN
  rfl

def realMinMaxToEventFlow : RealMinMaxUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        realMinMaxEncodeBHist X,
        realMinMaxEncodeBHist Y,
        realMinMaxEncodeBHist RX,
        realMinMaxEncodeBHist RY,
        realMinMaxEncodeBHist SX,
        realMinMaxEncodeBHist SY,
        realMinMaxEncodeBHist D,
        realMinMaxEncodeBHist E,
        realMinMaxEncodeBHist C,
        realMinMaxEncodeBHist O,
        realMinMaxEncodeBHist L,
        realMinMaxEncodeBHist U,
        realMinMaxEncodeBHist H,
        realMinMaxEncodeBHist T,
        realMinMaxEncodeBHist P,
        realMinMaxEncodeBHist N]

def realMinMaxFromEventFlow : EventFlow → Option RealMinMaxUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restX =>
      match restX with
      | [] => none
      | X :: restY =>
          match restY with
          | [] => none
          | Y :: restRX =>
              match restRX with
              | [] => none
              | RX :: restRY =>
                  match restRY with
                  | [] => none
                  | RY :: restSX =>
                      match restSX with
                      | [] => none
                      | SX :: restSY =>
                          match restSY with
                          | [] => none
                          | SY :: restD =>
                              match restD with
                              | [] => none
                              | D :: restE =>
                                  match restE with
                                  | [] => none
                                  | E :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restO =>
                                          match restO with
                                          | [] => none
                                          | O :: restL =>
                                              match restL with
                                              | [] => none
                                              | L :: restU =>
                                                  match restU with
                                                  | [] => none
                                                  | U :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | H :: restT =>
                                                          match restT with
                                                          | [] => none
                                                          | T :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restN =>
                                                                  match restN with
                                                                  | [] => none
                                                                  | N :: rest =>
                                                                      match rest with
                                                                      | [] =>
                                                                          some
                                                                            (RealMinMaxUp.mk
                                                                              (realMinMaxDecodeBHist X)
                                                                              (realMinMaxDecodeBHist Y)
                                                                              (realMinMaxDecodeBHist RX)
                                                                              (realMinMaxDecodeBHist RY)
                                                                              (realMinMaxDecodeBHist SX)
                                                                              (realMinMaxDecodeBHist SY)
                                                                              (realMinMaxDecodeBHist D)
                                                                              (realMinMaxDecodeBHist E)
                                                                              (realMinMaxDecodeBHist C)
                                                                              (realMinMaxDecodeBHist O)
                                                                              (realMinMaxDecodeBHist L)
                                                                              (realMinMaxDecodeBHist U)
                                                                              (realMinMaxDecodeBHist H)
                                                                              (realMinMaxDecodeBHist T)
                                                                              (realMinMaxDecodeBHist P)
                                                                              (realMinMaxDecodeBHist N))
                                                                      | _ :: _ => none

private theorem RealMinMaxTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealMinMaxUp, realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y RX RY SX SY D E C O L U H T P N =>
      change
        some
          (RealMinMaxUp.mk
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist X))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist Y))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist RX))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist RY))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist SX))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist SY))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist D))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist E))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist C))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist O))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist L))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist U))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist H))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist T))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist P))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist N))) =
          some (RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N)
      exact
        congrArg some
          (realMinMax_mk_congr
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode X)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode Y)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RX)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RY)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SX)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SY)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode D)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode E)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode C)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode O)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode L)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode U)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode H)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode T)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode P)
            (RealMinMaxTasteGate_single_carrier_alignment_decode_encode N))

private theorem RealMinMaxTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealMinMaxUp} :
    realMinMaxToEventFlow x = realMinMaxToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realMinMaxFromEventFlow (realMinMaxToEventFlow x) =
        realMinMaxFromEventFlow (realMinMaxToEventFlow y) :=
    congrArg realMinMaxFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealMinMaxTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealMinMaxTasteGate_single_carrier_alignment_round_trip y)))

private theorem realMinMax_field_faithful :
    ∀ x y : RealMinMaxUp, realMinMaxFields x = realMinMaxFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X₁ Y₁ RX₁ RY₁ SX₁ SY₁ D₁ E₁ C₁ O₁ L₁ U₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ RX₂ RY₂ SX₂ SY₂ D₂ E₂ C₂ O₂ L₂ U₂ H₂ T₂ P₂ N₂ =>
          cases h
          rfl

instance realMinMaxBHistCarrier : BHistCarrier RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realMinMaxToEventFlow
  fromEventFlow := realMinMaxFromEventFlow

instance realMinMaxChapterTasteGate : ChapterTasteGate RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x
    exact RealMinMaxTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealMinMaxTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realMinMaxFieldFaithful : FieldFaithful RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realMinMaxFields
  field_faithful := realMinMax_field_faithful

def taste_gate : ChapterTasteGate RealMinMaxUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realMinMaxChapterTasteGate

theorem RealMinMaxUp_single_carrier_alignment :
    (∀ h : BHist, realMinMaxDecodeBHist (realMinMaxEncodeBHist h) = h) ∧
      (∀ x : RealMinMaxUp, realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x) ∧
      (∀ x y : RealMinMaxUp,
        realMinMaxToEventFlow x = realMinMaxToEventFlow y → x = y) ∧
      realMinMaxEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealMinMaxTasteGate_single_carrier_alignment_decode_encode,
      RealMinMaxTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealMinMaxTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

theorem RealMinMaxTasteGate_single_carrier_alignment :
    (∀ h : BHist, realMinMaxDecodeBHist (realMinMaxEncodeBHist h) = h) ∧
      (∀ x : RealMinMaxUp, realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x) ∧
        (∀ x y : RealMinMaxUp,
          realMinMaxToEventFlow x = realMinMaxToEventFlow y → x = y) ∧
          realMinMaxEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk X Y RX RY SX SY D E C O L U H T P N =>
          change
            some
              (RealMinMaxUp.mk
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist X))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist Y))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist RX))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist RY))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist SX))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist SY))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist D))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist E))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist C))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist O))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist L))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist U))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist H))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist T))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist P))
                (realMinMaxDecodeBHist (realMinMaxEncodeBHist N))) =
              some (RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N)
          exact
            congrArg some
              (realMinMax_mk_congr
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode X)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode Y)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RX)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RY)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SX)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SY)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode D)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode E)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode C)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode O)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode L)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode U)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode H)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode T)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode P)
                (RealMinMaxTasteGate_single_carrier_alignment_decode_encode N))
    · constructor
      · intro x y heq
        have hread :
            realMinMaxFromEventFlow (realMinMaxToEventFlow x) =
              realMinMaxFromEventFlow (realMinMaxToEventFlow y) :=
          congrArg realMinMaxFromEventFlow heq
        have hx :
            realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x := by
          cases x with
          | mk X Y RX RY SX SY D E C O L U H T P N =>
              change
                some
                  (RealMinMaxUp.mk
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist X))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist Y))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist RX))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist RY))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist SX))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist SY))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist D))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist E))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist C))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist O))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist L))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist U))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist H))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist T))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist P))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist N))) =
                  some (RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N)
              exact
                congrArg some
                  (realMinMax_mk_congr
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode X)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode Y)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RX)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RY)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SX)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SY)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode D)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode E)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode C)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode O)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode L)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode U)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode H)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode T)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode P)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode N))
        have hy :
            realMinMaxFromEventFlow (realMinMaxToEventFlow y) = some y := by
          cases y with
          | mk X Y RX RY SX SY D E C O L U H T P N =>
              change
                some
                  (RealMinMaxUp.mk
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist X))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist Y))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist RX))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist RY))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist SX))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist SY))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist D))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist E))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist C))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist O))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist L))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist U))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist H))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist T))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist P))
                    (realMinMaxDecodeBHist (realMinMaxEncodeBHist N))) =
                  some (RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N)
              exact
                congrArg some
                  (realMinMax_mk_congr
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode X)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode Y)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RX)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode RY)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SX)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode SY)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode D)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode E)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode C)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode O)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode L)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode U)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode H)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode T)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode P)
                    (RealMinMaxTasteGate_single_carrier_alignment_decode_encode N))
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · rfl

end BEDC.Derived.RealMinMaxUp

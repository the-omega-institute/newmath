import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalWindowRealSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalWindowRealSealUp : Type where
  | mk (B T W D R E X G H C P N : BHist) : CofinalWindowRealSealUp
  deriving DecidableEq

def cofinalWindowRealSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalWindowRealSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalWindowRealSealEncodeBHist h

def cofinalWindowRealSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalWindowRealSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalWindowRealSealDecodeBHist tail)

private theorem cofinalWindowRealSeal_decode_encode_bhist :
    ∀ h : BHist, cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalWindowRealSealFields : CofinalWindowRealSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalWindowRealSealUp.mk B T W D R E X G H C P N =>
      [B, T, W, D, R, E, X, G, H, C, P, N]

def cofinalWindowRealSealToEventFlow : CofinalWindowRealSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalWindowRealSealUp.mk B T W D R E X G H C P N =>
      [cofinalWindowRealSealEncodeBHist B,
        cofinalWindowRealSealEncodeBHist T,
        cofinalWindowRealSealEncodeBHist W,
        cofinalWindowRealSealEncodeBHist D,
        cofinalWindowRealSealEncodeBHist R,
        cofinalWindowRealSealEncodeBHist E,
        cofinalWindowRealSealEncodeBHist X,
        cofinalWindowRealSealEncodeBHist G,
        cofinalWindowRealSealEncodeBHist H,
        cofinalWindowRealSealEncodeBHist C,
        cofinalWindowRealSealEncodeBHist P,
        cofinalWindowRealSealEncodeBHist N]

def cofinalWindowRealSealFromEventFlow :
    EventFlow → Option CofinalWindowRealSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | X :: rest6 =>
                              match rest6 with
                              | [] => none
                              | G :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CofinalWindowRealSealUp.mk
                                                          (cofinalWindowRealSealDecodeBHist B)
                                                          (cofinalWindowRealSealDecodeBHist T)
                                                          (cofinalWindowRealSealDecodeBHist W)
                                                          (cofinalWindowRealSealDecodeBHist D)
                                                          (cofinalWindowRealSealDecodeBHist R)
                                                          (cofinalWindowRealSealDecodeBHist E)
                                                          (cofinalWindowRealSealDecodeBHist X)
                                                          (cofinalWindowRealSealDecodeBHist G)
                                                          (cofinalWindowRealSealDecodeBHist H)
                                                          (cofinalWindowRealSealDecodeBHist C)
                                                          (cofinalWindowRealSealDecodeBHist P)
                                                          (cofinalWindowRealSealDecodeBHist N))
                                                  | _ :: _ => none

private theorem cofinalWindowRealSeal_round_trip :
    ∀ x : CofinalWindowRealSealUp,
      cofinalWindowRealSealFromEventFlow (cofinalWindowRealSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T W D R E X G H C P N =>
      change
        some
          (CofinalWindowRealSealUp.mk
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist B))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist T))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist W))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist D))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist R))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist E))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist X))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist G))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist H))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist C))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist P))
            (cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist N))) =
          some (CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
      rw [cofinalWindowRealSeal_decode_encode_bhist B,
        cofinalWindowRealSeal_decode_encode_bhist T,
        cofinalWindowRealSeal_decode_encode_bhist W,
        cofinalWindowRealSeal_decode_encode_bhist D,
        cofinalWindowRealSeal_decode_encode_bhist R,
        cofinalWindowRealSeal_decode_encode_bhist E,
        cofinalWindowRealSeal_decode_encode_bhist X,
        cofinalWindowRealSeal_decode_encode_bhist G,
        cofinalWindowRealSeal_decode_encode_bhist H,
        cofinalWindowRealSeal_decode_encode_bhist C,
        cofinalWindowRealSeal_decode_encode_bhist P,
        cofinalWindowRealSeal_decode_encode_bhist N]

private theorem cofinalWindowRealSealToEventFlow_injective
    {x y : CofinalWindowRealSealUp} :
    cofinalWindowRealSealToEventFlow x = cofinalWindowRealSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalWindowRealSealFromEventFlow (cofinalWindowRealSealToEventFlow x) =
        cofinalWindowRealSealFromEventFlow (cofinalWindowRealSealToEventFlow y) :=
    congrArg cofinalWindowRealSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalWindowRealSeal_round_trip x).symm
      (Eq.trans hread (cofinalWindowRealSeal_round_trip y)))

private theorem cofinalWindowRealSeal_field_faithful :
    ∀ x y : CofinalWindowRealSealUp,
      cofinalWindowRealSealFields x = cofinalWindowRealSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B₁ T₁ W₁ D₁ R₁ E₁ X₁ G₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ T₂ W₂ D₂ R₂ E₂ X₂ G₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance cofinalWindowRealSealBHistCarrier : BHistCarrier CofinalWindowRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalWindowRealSealToEventFlow
  fromEventFlow := cofinalWindowRealSealFromEventFlow

instance cofinalWindowRealSealChapterTasteGate :
    ChapterTasteGate CofinalWindowRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalWindowRealSealFromEventFlow (cofinalWindowRealSealToEventFlow x) = some x
    exact cofinalWindowRealSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalWindowRealSealToEventFlow_injective heq)

instance cofinalWindowRealSealFieldFaithful : FieldFaithful CofinalWindowRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalWindowRealSealFields
  field_faithful := cofinalWindowRealSeal_field_faithful

instance cofinalWindowRealSealNontrivial : Nontrivial CofinalWindowRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalWindowRealSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CofinalWindowRealSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalWindowRealSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalWindowRealSealChapterTasteGate

theorem CofinalWindowRealSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalWindowRealSealDecodeBHist (cofinalWindowRealSealEncodeBHist h) = h) ∧
      (∀ x : CofinalWindowRealSealUp,
        cofinalWindowRealSealFromEventFlow (cofinalWindowRealSealToEventFlow x) = some x) ∧
      (∀ x y : CofinalWindowRealSealUp,
        cofinalWindowRealSealToEventFlow x = cofinalWindowRealSealToEventFlow y → x = y) ∧
      Nonempty
        (@ChapterTasteGate CofinalWindowRealSealUp cofinalWindowRealSealBHistCarrier) ∧
      (∀ x y : CofinalWindowRealSealUp,
        cofinalWindowRealSealFields x = cofinalWindowRealSealFields y → x = y) ∧
      cofinalWindowRealSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cofinalWindowRealSeal_decode_encode_bhist, cofinalWindowRealSeal_round_trip,
    fun _ _ heq => cofinalWindowRealSealToEventFlow_injective heq,
    ⟨cofinalWindowRealSealChapterTasteGate⟩, cofinalWindowRealSeal_field_faithful, rfl⟩

theorem CofinalWindowRealSeal_source_exhaustion {flow : EventFlow}
    {B T W D R E X G H C P N : BHist}
    (hflow :
      cofinalWindowRealSealFromEventFlow flow =
        some (CofinalWindowRealSealUp.mk B T W D R E X G H C P N)) :
    ∃ (eB eT eW eD eR eE eX eG : List BMark) (tail : EventFlow),
      flow = eB :: eT :: eW :: eD :: eR :: eE :: eX :: eG :: tail ∧
        cofinalWindowRealSealDecodeBHist eB = B ∧
          cofinalWindowRealSealDecodeBHist eT = T ∧
            cofinalWindowRealSealDecodeBHist eW = W ∧
              cofinalWindowRealSealDecodeBHist eD = D ∧
                cofinalWindowRealSealDecodeBHist eR = R ∧
                  cofinalWindowRealSealDecodeBHist eE = E ∧
                    cofinalWindowRealSealDecodeBHist eX = X ∧
                      cofinalWindowRealSealDecodeBHist eG = G := by
  -- BEDC touchpoint anchor: BHist BMark
  cases flow with
  | nil =>
      cases hflow
  | cons eB rest0 =>
      cases rest0 with
      | nil =>
          cases hflow
      | cons eT rest1 =>
          cases rest1 with
          | nil =>
              cases hflow
          | cons eW rest2 =>
              cases rest2 with
              | nil =>
                  cases hflow
              | cons eD rest3 =>
                  cases rest3 with
                  | nil =>
                      cases hflow
                  | cons eR rest4 =>
                      cases rest4 with
                      | nil =>
                          cases hflow
                      | cons eE rest5 =>
                          cases rest5 with
                          | nil =>
                              cases hflow
                          | cons eX rest6 =>
                              cases rest6 with
                              | nil =>
                                  cases hflow
                              | cons eG rest7 =>
                                  cases rest7 with
                                  | nil =>
                                      cases hflow
                                  | cons eH rest8 =>
                                      cases rest8 with
                                      | nil =>
                                          cases hflow
                                      | cons eC rest9 =>
                                          cases rest9 with
                                          | nil =>
                                              cases hflow
                                          | cons eP rest10 =>
                                              cases rest10 with
                                              | nil =>
                                                  cases hflow
                                              | cons eN rest11 =>
                                                  cases rest11 with
                                                  | nil =>
                                                      injection hflow with hmk
                                                      cases hmk
                                                      exact ⟨eB, eT, eW, eD, eR, eE, eX, eG,
                                                        [eH, eC, eP, eN], rfl, rfl, rfl,
                                                        rfl, rfl, rfl, rfl, rfl, rfl⟩
                                                  | cons _ _ =>
                                                      cases hflow

end BEDC.Derived.CofinalWindowRealSealUp

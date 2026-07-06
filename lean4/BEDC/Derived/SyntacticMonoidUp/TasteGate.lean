import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SyntacticMonoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SyntacticMonoidUp : Type where
  | mk (A W L E C mu e rho H K P N : BHist) : SyntacticMonoidUp
  deriving DecidableEq

def syntacticMonoidEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: syntacticMonoidEncodeBHist h
  | BHist.e1 h => BMark.b1 :: syntacticMonoidEncodeBHist h

def syntacticMonoidDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (syntacticMonoidDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (syntacticMonoidDecodeBHist tail)

private theorem syntacticMonoidDecode_encode_bhist :
    ∀ h : BHist, syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def syntacticMonoidToEventFlow : SyntacticMonoidUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SyntacticMonoidUp.mk A W L E C mu e rho H K P N =>
      [syntacticMonoidEncodeBHist A,
        syntacticMonoidEncodeBHist W,
        syntacticMonoidEncodeBHist L,
        syntacticMonoidEncodeBHist E,
        syntacticMonoidEncodeBHist C,
        syntacticMonoidEncodeBHist mu,
        syntacticMonoidEncodeBHist e,
        syntacticMonoidEncodeBHist rho,
        syntacticMonoidEncodeBHist H,
        syntacticMonoidEncodeBHist K,
        syntacticMonoidEncodeBHist P,
        syntacticMonoidEncodeBHist N]

def syntacticMonoidFromEventFlow : EventFlow → Option SyntacticMonoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | mu :: rest5 =>
                          match rest5 with
                          | [] => none
                          | e :: rest6 =>
                              match rest6 with
                              | [] => none
                              | rho :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | K :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (SyntacticMonoidUp.mk
                                                          (syntacticMonoidDecodeBHist A)
                                                          (syntacticMonoidDecodeBHist W)
                                                          (syntacticMonoidDecodeBHist L)
                                                          (syntacticMonoidDecodeBHist E)
                                                          (syntacticMonoidDecodeBHist C)
                                                          (syntacticMonoidDecodeBHist mu)
                                                          (syntacticMonoidDecodeBHist e)
                                                          (syntacticMonoidDecodeBHist rho)
                                                          (syntacticMonoidDecodeBHist H)
                                                          (syntacticMonoidDecodeBHist K)
                                                          (syntacticMonoidDecodeBHist P)
                                                          (syntacticMonoidDecodeBHist N))
                                                  | _ :: _ => none

private theorem syntacticMonoid_round_trip :
    ∀ x : SyntacticMonoidUp,
      syntacticMonoidFromEventFlow (syntacticMonoidToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W L E C mu e rho H K P N =>
      change
        some
          (SyntacticMonoidUp.mk
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist A))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist W))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist L))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist E))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist C))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist mu))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist e))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist rho))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist H))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist K))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist P))
            (syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist N))) =
          some (SyntacticMonoidUp.mk A W L E C mu e rho H K P N)
      rw [syntacticMonoidDecode_encode_bhist A,
        syntacticMonoidDecode_encode_bhist W,
        syntacticMonoidDecode_encode_bhist L,
        syntacticMonoidDecode_encode_bhist E,
        syntacticMonoidDecode_encode_bhist C,
        syntacticMonoidDecode_encode_bhist mu,
        syntacticMonoidDecode_encode_bhist e,
        syntacticMonoidDecode_encode_bhist rho,
        syntacticMonoidDecode_encode_bhist H,
        syntacticMonoidDecode_encode_bhist K,
        syntacticMonoidDecode_encode_bhist P,
        syntacticMonoidDecode_encode_bhist N]

private theorem syntacticMonoidToEventFlow_injective
    {x y : SyntacticMonoidUp} :
    syntacticMonoidToEventFlow x = syntacticMonoidToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          syntacticMonoidFromEventFlow (syntacticMonoidToEventFlow x) :=
        (syntacticMonoid_round_trip x).symm
      _ = syntacticMonoidFromEventFlow (syntacticMonoidToEventFlow y) :=
        congrArg syntacticMonoidFromEventFlow hxy
      _ = some y := syntacticMonoid_round_trip y
  exact Option.some.inj optionEq

instance syntacticMonoidBHistCarrier : BHistCarrier SyntacticMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := syntacticMonoidToEventFlow
  fromEventFlow := syntacticMonoidFromEventFlow

instance syntacticMonoidChapterTasteGate : ChapterTasteGate SyntacticMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change syntacticMonoidFromEventFlow (syntacticMonoidToEventFlow x) = some x
    exact syntacticMonoid_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (syntacticMonoidToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SyntacticMonoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  syntacticMonoidChapterTasteGate

theorem SyntacticMonoidTasteGate_single_carrier_alignment :
    (Exists fun carrier : BHistCarrier SyntacticMonoidUp =>
      Nonempty (@ChapterTasteGate SyntacticMonoidUp carrier)) ∧
      (∀ h : BHist, syntacticMonoidDecodeBHist (syntacticMonoidEncodeBHist h) = h) ∧
        (∀ x : SyntacticMonoidUp,
          syntacticMonoidFromEventFlow (syntacticMonoidToEventFlow x) = some x) ∧
          syntacticMonoidEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨syntacticMonoidBHistCarrier, Nonempty.intro syntacticMonoidChapterTasteGate⟩,
      syntacticMonoidDecode_encode_bhist,
      syntacticMonoid_round_trip,
      rfl⟩

end BEDC.Derived.SyntacticMonoidUp

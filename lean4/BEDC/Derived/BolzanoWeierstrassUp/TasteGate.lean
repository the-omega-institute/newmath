import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BolzanoWeierstrassUp : Type where
  | mk
      (S K R Q E H C P N : BHist) :
      BolzanoWeierstrassUp
  deriving DecidableEq

def bolzanoWeierstrassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bolzanoWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bolzanoWeierstrassEncodeBHist h

def bolzanoWeierstrassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bolzanoWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bolzanoWeierstrassDecodeBHist tail)

private theorem BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bolzanoWeierstrassToEventFlow : BolzanoWeierstrassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BolzanoWeierstrassUp.mk S K R Q E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        bolzanoWeierstrassEncodeBHist S,
        bolzanoWeierstrassEncodeBHist K,
        bolzanoWeierstrassEncodeBHist R,
        bolzanoWeierstrassEncodeBHist Q,
        bolzanoWeierstrassEncodeBHist E,
        bolzanoWeierstrassEncodeBHist H,
        bolzanoWeierstrassEncodeBHist C,
        bolzanoWeierstrassEncodeBHist P,
        bolzanoWeierstrassEncodeBHist N]

def bolzanoWeierstrassFromEventFlow : EventFlow → Option BolzanoWeierstrassUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restS =>
      match restS with
      | [] => none
      | S :: restK =>
          match restK with
          | [] => none
          | K :: restR =>
              match restR with
              | [] => none
              | R :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restE =>
                      match restE with
                      | [] => none
                      | E :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (BolzanoWeierstrassUp.mk
                                                  (bolzanoWeierstrassDecodeBHist S)
                                                  (bolzanoWeierstrassDecodeBHist K)
                                                  (bolzanoWeierstrassDecodeBHist R)
                                                  (bolzanoWeierstrassDecodeBHist Q)
                                                  (bolzanoWeierstrassDecodeBHist E)
                                                  (bolzanoWeierstrassDecodeBHist H)
                                                  (bolzanoWeierstrassDecodeBHist C)
                                                  (bolzanoWeierstrassDecodeBHist P)
                                                  (bolzanoWeierstrassDecodeBHist N))
                                          | _ :: _ => none

private theorem BolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BolzanoWeierstrassUp,
      bolzanoWeierstrassFromEventFlow (bolzanoWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S K R Q E H C P N =>
      change
        some
          (BolzanoWeierstrassUp.mk
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist S))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist K))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist R))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist Q))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist E))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist H))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist C))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist P))
            (bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist N))) =
          some (BolzanoWeierstrassUp.mk S K R Q E H C P N)
      rw [BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode S,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode K,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode R,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode Q,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode E,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode H,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode C,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode P,
        BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode N]

private theorem BolzanoWeierstrassTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BolzanoWeierstrassUp} :
    bolzanoWeierstrassToEventFlow x = bolzanoWeierstrassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bolzanoWeierstrassFromEventFlow (bolzanoWeierstrassToEventFlow x) =
        bolzanoWeierstrassFromEventFlow (bolzanoWeierstrassToEventFlow y) :=
    congrArg bolzanoWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip y)))

instance bolzanoWeierstrassBHistCarrier : BHistCarrier BolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bolzanoWeierstrassToEventFlow
  fromEventFlow := bolzanoWeierstrassFromEventFlow

instance bolzanoWeierstrassChapterTasteGate : ChapterTasteGate BolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bolzanoWeierstrassFromEventFlow (bolzanoWeierstrassToEventFlow x) = some x
    exact BolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BolzanoWeierstrassTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BolzanoWeierstrassTasteGate_single_carrier_alignment :
    (∀ h : BHist, bolzanoWeierstrassDecodeBHist (bolzanoWeierstrassEncodeBHist h) = h) ∧
      (∀ x : BolzanoWeierstrassUp,
        bolzanoWeierstrassFromEventFlow (bolzanoWeierstrassToEventFlow x) = some x) ∧
        (∀ x y : BolzanoWeierstrassUp,
          bolzanoWeierstrassToEventFlow x = bolzanoWeierstrassToEventFlow y → x = y) ∧
          bolzanoWeierstrassEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode,
      BolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => BolzanoWeierstrassTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

theorem BolzanoWeierstrass_tagged_fromEventFlow_exactness :
    (∀ raw : List BMark, bolzanoWeierstrassEncodeBHist (bolzanoWeierstrassDecodeBHist raw) = raw) ∧
      (∀ {flow : EventFlow} {x : BolzanoWeierstrassUp},
        bolzanoWeierstrassFromEventFlow flow = some x →
          (∃ rest : EventFlow, flow = [BMark.b1, BMark.b0, BMark.b1, BMark.b0] :: rest) →
            bolzanoWeierstrassToEventFlow x = flow) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  have hraw :
      ∀ raw : List BMark, bolzanoWeierstrassEncodeBHist (bolzanoWeierstrassDecodeBHist raw) = raw := by
    intro raw
    induction raw with
    | nil => rfl
    | cons head tail ih =>
        cases head
        · change BMark.b0 :: bolzanoWeierstrassEncodeBHist
              (bolzanoWeierstrassDecodeBHist tail) = BMark.b0 :: tail
          exact congrArg (fun row => BMark.b0 :: row) ih
        · change BMark.b1 :: bolzanoWeierstrassEncodeBHist
              (bolzanoWeierstrassDecodeBHist tail) = BMark.b1 :: tail
          exact congrArg (fun row => BMark.b1 :: row) ih
  constructor
  · exact hraw
  · intro flow x h htag
    rcases htag with ⟨rest, hflow⟩
    cases hflow
    cases rest with
    | nil =>
        change none = some x at h
        cases h
    | cons S restS =>
        cases restS with
        | nil =>
            change none = some x at h
            cases h
        | cons K restK =>
            cases restK with
            | nil =>
                change none = some x at h
                cases h
            | cons R restR =>
                cases restR with
                | nil =>
                    change none = some x at h
                    cases h
                | cons Q restQ =>
                    cases restQ with
                    | nil =>
                        change none = some x at h
                        cases h
                    | cons E restE =>
                        cases restE with
                        | nil =>
                            change none = some x at h
                            cases h
                        | cons H restH =>
                            cases restH with
                            | nil =>
                                change none = some x at h
                                cases h
                            | cons C restC =>
                                cases restC with
                                | nil =>
                                    change none = some x at h
                                    cases h
                                | cons P restP =>
                                    cases restP with
                                    | nil =>
                                        change none = some x at h
                                        cases h
                                    | cons N restN =>
                                        cases restN with
                                        | nil =>
                                            change
                                              some
                                                (BolzanoWeierstrassUp.mk
                                                  (bolzanoWeierstrassDecodeBHist S)
                                                  (bolzanoWeierstrassDecodeBHist K)
                                                  (bolzanoWeierstrassDecodeBHist R)
                                                  (bolzanoWeierstrassDecodeBHist Q)
                                                  (bolzanoWeierstrassDecodeBHist E)
                                                  (bolzanoWeierstrassDecodeBHist H)
                                                  (bolzanoWeierstrassDecodeBHist C)
                                                  (bolzanoWeierstrassDecodeBHist P)
                                                  (bolzanoWeierstrassDecodeBHist N)) =
                                                some x at h
                                            cases h
                                            change
                                              [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist S),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist K),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist R),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist Q),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist E),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist H),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist C),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist P),
                                                bolzanoWeierstrassEncodeBHist
                                                  (bolzanoWeierstrassDecodeBHist N)] =
                                              [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
                                                S, K, R, Q, E, H, C, P, N]
                                            rw [hraw S, hraw K, hraw R, hraw Q, hraw E, hraw H,
                                              hraw C, hraw P, hraw N]
                                        | cons _ _ =>
                                            change none = some x at h
                                            cases h

end BEDC.Derived.BolzanoWeierstrassUp

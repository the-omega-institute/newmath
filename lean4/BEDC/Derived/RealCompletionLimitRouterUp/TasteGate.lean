import BEDC.FKernel.NameCert
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionLimitRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionLimitRouterUp : Type where
  | mk : (O W Q D E H C P N : BHist) → RealCompletionLimitRouterUp
  deriving DecidableEq

def realCompletionLimitRouterFields : RealCompletionLimitRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionLimitRouterUp.mk O W Q D E H C P N => [O, W, Q, D, E, H, C, P, N]

def realCompletionLimitRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionLimitRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionLimitRouterEncodeBHist h

def realCompletionLimitRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionLimitRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionLimitRouterDecodeBHist tail)

private theorem realCompletionLimitRouterDecodeEncodeBHist :
    ∀ h : BHist, realCompletionLimitRouterDecodeBHist
      (realCompletionLimitRouterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletionLimitRouterToEventFlow : RealCompletionLimitRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCompletionLimitRouterFields x).map realCompletionLimitRouterEncodeBHist

def realCompletionLimitRouterFromEventFlow : EventFlow → Option RealCompletionLimitRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | O :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RealCompletionLimitRouterUp.mk
                                              (realCompletionLimitRouterDecodeBHist O)
                                              (realCompletionLimitRouterDecodeBHist W)
                                              (realCompletionLimitRouterDecodeBHist Q)
                                              (realCompletionLimitRouterDecodeBHist D)
                                              (realCompletionLimitRouterDecodeBHist E)
                                              (realCompletionLimitRouterDecodeBHist H)
                                              (realCompletionLimitRouterDecodeBHist C)
                                              (realCompletionLimitRouterDecodeBHist P)
                                              (realCompletionLimitRouterDecodeBHist N))
                                      | _ :: _ => none

private theorem realCompletionLimitRouter_round_trip :
    ∀ x : RealCompletionLimitRouterUp,
      realCompletionLimitRouterFromEventFlow
        (realCompletionLimitRouterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O W Q D E H C P N =>
      change
        some
          (RealCompletionLimitRouterUp.mk
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist O))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist W))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist Q))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist D))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist E))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist H))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist C))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist P))
            (realCompletionLimitRouterDecodeBHist (realCompletionLimitRouterEncodeBHist N))) =
          some (RealCompletionLimitRouterUp.mk O W Q D E H C P N)
      rw [realCompletionLimitRouterDecodeEncodeBHist O,
        realCompletionLimitRouterDecodeEncodeBHist W,
        realCompletionLimitRouterDecodeEncodeBHist Q,
        realCompletionLimitRouterDecodeEncodeBHist D,
        realCompletionLimitRouterDecodeEncodeBHist E,
        realCompletionLimitRouterDecodeEncodeBHist H,
        realCompletionLimitRouterDecodeEncodeBHist C,
        realCompletionLimitRouterDecodeEncodeBHist P,
        realCompletionLimitRouterDecodeEncodeBHist N]

private theorem realCompletionLimitRouterToEventFlow_injective
    {x y : RealCompletionLimitRouterUp} :
    realCompletionLimitRouterToEventFlow x = realCompletionLimitRouterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionLimitRouterFromEventFlow (realCompletionLimitRouterToEventFlow x) =
        realCompletionLimitRouterFromEventFlow (realCompletionLimitRouterToEventFlow y) :=
    congrArg realCompletionLimitRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionLimitRouter_round_trip x).symm
      (Eq.trans hread (realCompletionLimitRouter_round_trip y)))

instance realCompletionLimitRouterBHistCarrier : BHistCarrier RealCompletionLimitRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionLimitRouterToEventFlow
  fromEventFlow := realCompletionLimitRouterFromEventFlow

instance realCompletionLimitRouterChapterTasteGate :
    ChapterTasteGate RealCompletionLimitRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionLimitRouterFromEventFlow
      (realCompletionLimitRouterToEventFlow x) = some x
    exact realCompletionLimitRouter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionLimitRouterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCompletionLimitRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionLimitRouterFromEventFlow
      (realCompletionLimitRouterToEventFlow x) = some x
    exact realCompletionLimitRouter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionLimitRouterToEventFlow_injective heq)

theorem RealCompletionLimitRouterCarrier_namecert_obligations
    (O W Q D E H C P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row O ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        hsame ∧
      realCompletionLimitRouterFields (RealCompletionLimitRouterUp.mk O W Q D E H C P N) =
        [O, W, Q, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: RealCompletionLimitRouterUp BHist hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro O (Or.inl (hsame_refl O))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          cases source with
          | inl sameO =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameO)
          | inr rest =>
              cases rest with
              | inl sameW =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW))
              | inr rest =>
                  cases rest with
                  | inl sameQ =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ)))
                  | inr rest =>
                      cases rest with
                      | inl sameD =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameD))))
                      | inr rest =>
                          cases rest with
                          | inl sameE =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameE)))))
                          | inr rest =>
                              cases rest with
                              | inl sameH =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameH))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameC =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameC)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameP =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameP))))))))
                                      | inr sameN =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameN))))))))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · rfl

end BEDC.Derived.RealCompletionLimitRouterUp

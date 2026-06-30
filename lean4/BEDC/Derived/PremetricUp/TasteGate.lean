import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PremetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PremetricUp : Type where
  | mk (X U D Z S M H C Q N : BHist) : PremetricUp
  deriving DecidableEq

def PremetricTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: PremetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: PremetricTasteGate_single_carrier_alignment_encodeBHist h

def PremetricTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (PremetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (PremetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem PremetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      PremetricTasteGate_single_carrier_alignment_decodeBHist
        (PremetricTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PremetricTasteGate_single_carrier_alignment_fields :
    PremetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PremetricUp.mk X U D Z S M H C Q N => [X, U, D, Z, S, M, H, C, Q, N]

def PremetricTasteGate_single_carrier_alignment_toEventFlow :
    PremetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (PremetricTasteGate_single_carrier_alignment_fields x).map
      PremetricTasteGate_single_carrier_alignment_encodeBHist

def PremetricTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option PremetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | X :: U :: D :: Z :: S :: M :: H :: C :: Q :: N :: [] =>
        some
          (PremetricUp.mk
            (PremetricTasteGate_single_carrier_alignment_decodeBHist X)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist U)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist D)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist Z)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist S)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist M)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist H)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist C)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist Q)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist N))
    | _ => none

private theorem PremetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PremetricUp,
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
        (PremetricTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U D Z S M H C Q N =>
      change
        some
          (PremetricUp.mk
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist X))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist U))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist D))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist Z))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist S))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist M))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist H))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist C))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist Q))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (PremetricUp.mk X U D Z S M H C Q N)
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode X]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode U]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode D]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode Z]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode S]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode M]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode H]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode C]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode Q]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem PremetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PremetricUp} :
    PremetricTasteGate_single_carrier_alignment_toEventFlow x =
        PremetricTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
          (PremetricTasteGate_single_carrier_alignment_toEventFlow x) =
        PremetricTasteGate_single_carrier_alignment_fromEventFlow
          (PremetricTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg PremetricTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PremetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PremetricTasteGate_single_carrier_alignment_round_trip y)))

instance premetricBHistCarrier : BHistCarrier PremetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PremetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := PremetricTasteGate_single_carrier_alignment_fromEventFlow

instance premetricChapterTasteGate : ChapterTasteGate PremetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
        (PremetricTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact PremetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PremetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PremetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  premetricChapterTasteGate

theorem PremetricTasteGate_single_carrier_alignment :
    (∀ X U D Z S M H C Q N : BHist,
      PremetricTasteGate_single_carrier_alignment_fields
          (PremetricUp.mk X U D Z S M H C Q N) =
        [X, U, D, Z, S, M, H, C, Q, N]) ∧
      (∀ h : BHist,
        PremetricTasteGate_single_carrier_alignment_decodeBHist
          (PremetricTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        PremetricTasteGate_single_carrier_alignment_encodeBHist (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨by
      intro X U D Z S M H C Q N
      rfl,
      PremetricTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

theorem PremetricSeparatedReflectionRoute
    {X U D Z S M H C Q N uniformRead zeroRead reflectionRead : BHist} :
    UnaryHistory X → UnaryHistory U → UnaryHistory D → UnaryHistory Z →
      UnaryHistory S → UnaryHistory M → UnaryHistory H → UnaryHistory C →
        UnaryHistory Q → UnaryHistory N →
          Cont X U uniformRead → Cont D Z zeroRead →
            Cont uniformRead zeroRead reflectionRead →
              SemanticNameCert
                  (fun row : BHist => hsame row reflectionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨
                      hsame row S ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                        hsame row Q ∨ hsame row N ∨ hsame row reflectionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X U uniformRead ∧ Cont D Z zeroRead ∧
                      Cont uniformRead zeroRead reflectionRead)
                  hsame ∧ UnaryHistory reflectionRead := by
  -- BEDC touchpoint anchor: PremetricUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro xUnary uUnary dUnary zUnary _sUnary _mUnary _hUnary _cUnary _qUnary _nUnary
    uniformRoute zeroRoute reflectionRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed xUnary uUnary uniformRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed dUnary zUnary zeroRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed uniformUnary zeroUnary reflectionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reflectionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨
              hsame row S ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                hsame row Q ∨ hsame row N ∨ hsame row reflectionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X U uniformRead ∧ Cont D Z zeroRead ∧
              Cont uniformRead zeroRead reflectionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro reflectionRead
        ⟨hsame_refl reflectionRead, reflectionUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceData.left)))))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, uniformRoute, zeroRoute, reflectionRoute⟩
  }
  exact ⟨cert, reflectionUnary⟩

end BEDC.Derived.PremetricUp

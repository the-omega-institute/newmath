import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

inductive AlgebraicExpressionLedgerUp : Type where
  | mk : (e o a u s h c p n : BHist) → AlgebraicExpressionLedgerUp
  deriving DecidableEq

namespace AlgebraicExpressionLedgerUp

def algebraicExpressionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: algebraicExpressionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: algebraicExpressionLedgerEncodeBHist h

def algebraicExpressionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (algebraicExpressionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (algebraicExpressionLedgerDecodeBHist tail)

private theorem AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      algebraicExpressionLedgerDecodeBHist
          (algebraicExpressionLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def algebraicExpressionLedgerToEventFlow : AlgebraicExpressionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AlgebraicExpressionLedgerUp.mk e o a u s h c p n =>
      [algebraicExpressionLedgerEncodeBHist e,
        algebraicExpressionLedgerEncodeBHist o,
        algebraicExpressionLedgerEncodeBHist a,
        algebraicExpressionLedgerEncodeBHist u,
        algebraicExpressionLedgerEncodeBHist s,
        algebraicExpressionLedgerEncodeBHist h,
        algebraicExpressionLedgerEncodeBHist c,
        algebraicExpressionLedgerEncodeBHist p,
        algebraicExpressionLedgerEncodeBHist n]

def algebraicExpressionLedgerFromEventFlow :
    EventFlow → Option AlgebraicExpressionLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | e :: rest0 =>
      match rest0 with
      | [] => none
      | o :: rest1 =>
          match rest1 with
          | [] => none
          | a :: rest2 =>
              match rest2 with
              | [] => none
              | u :: rest3 =>
                  match rest3 with
                  | [] => none
                  | s :: rest4 =>
                      match rest4 with
                      | [] => none
                      | h :: rest5 =>
                          match rest5 with
                          | [] => none
                          | c :: rest6 =>
                              match rest6 with
                              | [] => none
                              | p :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | n :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (AlgebraicExpressionLedgerUp.mk
                                              (algebraicExpressionLedgerDecodeBHist e)
                                              (algebraicExpressionLedgerDecodeBHist o)
                                              (algebraicExpressionLedgerDecodeBHist a)
                                              (algebraicExpressionLedgerDecodeBHist u)
                                              (algebraicExpressionLedgerDecodeBHist s)
                                              (algebraicExpressionLedgerDecodeBHist h)
                                              (algebraicExpressionLedgerDecodeBHist c)
                                              (algebraicExpressionLedgerDecodeBHist p)
                                              (algebraicExpressionLedgerDecodeBHist n))
                                      | _ :: _ => none

private theorem AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_round_trip
    (x : AlgebraicExpressionLedgerUp) :
    algebraicExpressionLedgerFromEventFlow
        (algebraicExpressionLedgerToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk e o a u s h c p n =>
      change
        some
          (AlgebraicExpressionLedgerUp.mk
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist e))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist o))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist a))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist u))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist s))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist h))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist c))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist p))
            (algebraicExpressionLedgerDecodeBHist
              (algebraicExpressionLedgerEncodeBHist n))) =
          some (AlgebraicExpressionLedgerUp.mk e o a u s h c p n)
      rw [AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode e,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode o,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode a,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode u,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode s,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode h,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode c,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode p,
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode n]

private theorem AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlgebraicExpressionLedgerUp} :
    algebraicExpressionLedgerToEventFlow x =
        algebraicExpressionLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      algebraicExpressionLedgerFromEventFlow
          (algebraicExpressionLedgerToEventFlow x) =
        algebraicExpressionLedgerFromEventFlow
          (algebraicExpressionLedgerToEventFlow y) :=
    congrArg algebraicExpressionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_round_trip y)))

def AlgebraicExpressionLedgerCarrier
    (E O A U S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory E ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory U ∧
    UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N

theorem AlgebraicExpressionLedgerCarrier_namecert_obligations
    {E O A U S H C P N parseRead sealRead : BHist} :
    AlgebraicExpressionLedgerCarrier E O A U S H C P N →
      Cont E O parseRead →
        Cont parseRead C sealRead →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row E ∨ hsame row O ∨ hsame row A ∨ hsame row U ∨
                  hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row sealRead)
              (fun row : BHist =>
                hsame row sealRead ∧ Cont E O parseRead ∧ Cont parseRead C sealRead)
              hsame ∧
            UnaryHistory parseRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier parseRoute sealRoute
  have eUnary : UnaryHistory E := carrier.left
  have oUnary : UnaryHistory O := carrier.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.right.right.right.left
  have parseUnary : UnaryHistory parseRead :=
    unary_cont_closed eUnary oUnary parseRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed parseUnary cUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row O ∨ hsame row A ∨ hsame row U ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont E O parseRead ∧ Cont parseRead C sealRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, parseRoute, sealRoute⟩
  }
  exact ⟨cert, parseUnary, sealUnary⟩

theorem AlgebraicExpressionLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      algebraicExpressionLedgerDecodeBHist
          (algebraicExpressionLedgerEncodeBHist h) =
        h) ∧
      (∀ x : _root_.BEDC.Derived.AlgebraicExpressionLedgerUp,
        algebraicExpressionLedgerFromEventFlow
            (algebraicExpressionLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : _root_.BEDC.Derived.AlgebraicExpressionLedgerUp,
          algebraicExpressionLedgerToEventFlow x =
              algebraicExpressionLedgerToEventFlow y →
            x = y) ∧
          algebraicExpressionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_decode_encode,
      AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AlgebraicExpressionLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end AlgebraicExpressionLedgerUp

end BEDC.Derived

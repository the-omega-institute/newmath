import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealApartnessEqualityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealApartnessEqualityBoundaryUp : Type where
  | mk (R A D S Q T C P N : BHist) : BishopRealApartnessEqualityBoundaryUp
  deriving DecidableEq

def bishopRealApartnessEqualityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealApartnessEqualityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealApartnessEqualityBoundaryEncodeBHist h

def bishopRealApartnessEqualityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealApartnessEqualityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealApartnessEqualityBoundaryDecodeBHist tail)

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealApartnessEqualityBoundaryFields :
    BishopRealApartnessEqualityBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N =>
      [R, A, D, S, Q, T, C, P, N]

def bishopRealApartnessEqualityBoundaryToEventFlow :
    BishopRealApartnessEqualityBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopRealApartnessEqualityBoundaryFields x).map
      bishopRealApartnessEqualityBoundaryEncodeBHist

private def bishopRealApartnessEqualityBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopRealApartnessEqualityBoundaryEventAtDefault index rest

def bishopRealApartnessEqualityBoundaryFromEventFlow
    (ef : EventFlow) : Option BishopRealApartnessEqualityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealApartnessEqualityBoundaryUp.mk
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 0 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 1 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 2 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 3 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 4 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 5 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 6 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 7 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 8 ef)))

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealApartnessEqualityBoundaryUp,
      bishopRealApartnessEqualityBoundaryFromEventFlow
        (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A D S Q T C P N =>
      change
        some
          (BishopRealApartnessEqualityBoundaryUp.mk
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist R))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist A))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist D))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist S))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist Q))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist T))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist C))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist P))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist N))) =
          some (BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N)
      rw [BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode R,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode A,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode D,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode S,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode Q,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode T,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode C,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode P,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopRealApartnessEqualityBoundaryUp,
      bishopRealApartnessEqualityBoundaryFields x =
        bishopRealApartnessEqualityBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R A D S Q T C P N =>
      cases y with
      | mk R' A' D' S' Q' T' C' P' N' =>
          injection hfields with hR htail0
          injection htail0 with hA htail1
          injection htail1 with hD htail2
          injection htail2 with hS htail3
          injection htail3 with hQ htail4
          injection htail4 with hT htail5
          injection htail5 with hC htail6
          injection htail6 with hP htail7
          injection htail7 with hN _hNil
          cases hR
          cases hA
          cases hD
          cases hS
          cases hQ
          cases hT
          cases hC
          cases hP
          cases hN
          rfl

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealApartnessEqualityBoundaryUp} :
    bishopRealApartnessEqualityBoundaryToEventFlow x =
      bishopRealApartnessEqualityBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow x) =
        bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow y) :=
    congrArg bishopRealApartnessEqualityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealApartnessEqualityBoundaryBHistCarrier :
    BHistCarrier BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealApartnessEqualityBoundaryToEventFlow
  fromEventFlow := bishopRealApartnessEqualityBoundaryFromEventFlow

instance bishopRealApartnessEqualityBoundaryChapterTasteGate :
    ChapterTasteGate BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealApartnessEqualityBoundaryFromEventFlow
        (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x
    exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopRealApartnessEqualityBoundaryFieldFaithful :
    FieldFaithful BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealApartnessEqualityBoundaryFields
  field_faithful := BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BishopRealApartnessEqualityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRealApartnessEqualityBoundaryChapterTasteGate

theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEncodeBHist h) = h) ∧
      (∀ x : BishopRealApartnessEqualityBoundaryUp,
        bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x) ∧
        (∀ x y : BishopRealApartnessEqualityBoundaryUp,
          bishopRealApartnessEqualityBoundaryToEventFlow x =
            bishopRealApartnessEqualityBoundaryToEventFlow y → x = y) ∧
          bishopRealApartnessEqualityBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

theorem BishopRealApartnessEqualityBoundaryNameCertObligations
    (x : BishopRealApartnessEqualityBoundaryUp) :
    exists R A D S Q T C P N : BHist,
      x = BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N ∧
        bishopRealApartnessEqualityBoundaryFromEventFlow
            (bishopRealApartnessEqualityBoundaryToEventFlow x) =
          some x ∧
          SemanticNameCert
            (fun row : BHist =>
              hsame row R ∨ hsame row A ∨ hsame row D ∨ hsame row S ∨
                hsame row Q ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨
                  hsame row N)
            (fun row : BHist =>
              hsame row R ∨ hsame row A ∨ hsame row D ∨ hsame row S ∨
                hsame row Q ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨
                  hsame row N)
            (fun row : BHist =>
              hsame row R ∨ hsame row A ∨ hsame row D ∨ hsame row S ∨
                hsame row Q ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨
                  hsame row N)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert BishopRealApartnessEqualityBoundaryUp
  cases x with
  | mk R A D S Q T C P N =>
      refine Exists.intro R ?_
      refine Exists.intro A ?_
      refine Exists.intro D ?_
      refine Exists.intro S ?_
      refine Exists.intro Q ?_
      refine Exists.intro T ?_
      refine Exists.intro C ?_
      refine Exists.intro P ?_
      refine Exists.intro N ?_
      constructor
      · rfl
      · constructor
        · exact
            BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip
              (BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N)
        · exact {
            core := {
              carrier_inhabited := Exists.intro R (Or.inl (hsame_refl R))
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
                intro row other sameRows source
                cases sameRows
                exact source
            }
            pattern_sound := by
              intro _row source
              exact source
            ledger_sound := by
              intro _row source
              exact source
          }

theorem BishopRealApartnessEqualityBoundaryRealHandoff [AskSetup] [PackageSetup]
    {R A D S Q apartnessToDyadic dyadicToWindow windowToReadback readbackToReal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory D →
        UnaryHistory S →
          UnaryHistory Q →
            UnaryHistory R →
              Cont A D apartnessToDyadic →
                Cont apartnessToDyadic S dyadicToWindow →
                  Cont dyadicToWindow Q windowToReadback →
                    Cont windowToReadback R readbackToReal →
                      PkgSig bundle readbackToReal pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row readbackToReal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row A ∨ hsame row D ∨ hsame row S ∨ hsame row Q ∨
                                hsame row R ∨ hsame row readbackToReal)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont A D apartnessToDyadic ∧
                                Cont apartnessToDyadic S dyadicToWindow ∧
                                  Cont dyadicToWindow Q windowToReadback ∧
                                    Cont windowToReadback R readbackToReal ∧
                                      PkgSig bundle readbackToReal pkg)
                            hsame ∧
                          UnaryHistory apartnessToDyadic ∧ UnaryHistory dyadicToWindow ∧
                            UnaryHistory windowToReadback ∧ UnaryHistory readbackToReal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro aUnary dUnary sUnary qUnary rUnary aToD dToS sToQ qToR readbackPkg
  have apartnessUnary : UnaryHistory apartnessToDyadic :=
    unary_cont_closed aUnary dUnary aToD
  have dyadicUnary : UnaryHistory dyadicToWindow :=
    unary_cont_closed apartnessUnary sUnary dToS
  have windowUnary : UnaryHistory windowToReadback :=
    unary_cont_closed dyadicUnary qUnary sToQ
  have readbackUnary : UnaryHistory readbackToReal :=
    unary_cont_closed windowUnary rUnary qToR
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackToReal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row D ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row readbackToReal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A D apartnessToDyadic ∧
              Cont apartnessToDyadic S dyadicToWindow ∧
                Cont dyadicToWindow Q windowToReadback ∧
                  Cont windowToReadback R readbackToReal ∧
                    PkgSig bundle readbackToReal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackToReal ⟨hsame_refl readbackToReal, readbackUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, aToD, dToS, sToQ, qToR, readbackPkg⟩
  }
  exact ⟨cert, apartnessUnary, dyadicUnary, windowUnary, readbackUnary⟩

end BEDC.Derived.BishopRealApartnessEqualityBoundaryUp

import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyBinaryInterleavingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyBinaryInterleavingUp : Type where
  | mk (S0 S1 E O T R0 R1 L H K P N : BHist) : RegularCauchyBinaryInterleavingUp
  deriving DecidableEq

def regularCauchyBinaryInterleavingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyBinaryInterleavingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyBinaryInterleavingEncodeBHist h

def regularCauchyBinaryInterleavingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyBinaryInterleavingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyBinaryInterleavingDecodeBHist tail)

private theorem RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyBinaryInterleavingFields :
    RegularCauchyBinaryInterleavingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBinaryInterleavingUp.mk S0 S1 E O T R0 R1 L H K P N =>
      [S0, S1, E, O, T, R0, R1, L, H, K, P, N]

def regularCauchyBinaryInterleavingToEventFlow :
    RegularCauchyBinaryInterleavingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyBinaryInterleavingFields x).map
      regularCauchyBinaryInterleavingEncodeBHist

private def regularCauchyBinaryInterleavingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyBinaryInterleavingEventAt index rest

def regularCauchyBinaryInterleavingFromEventFlow
    (ef : EventFlow) : Option RegularCauchyBinaryInterleavingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyBinaryInterleavingUp.mk
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 0 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 1 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 2 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 3 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 4 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 5 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 6 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 7 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 8 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 9 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 10 ef))
      (regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEventAt 11 ef)))

private theorem RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyBinaryInterleavingUp) :
    regularCauchyBinaryInterleavingFromEventFlow
      (regularCauchyBinaryInterleavingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S0 S1 E O T R0 R1 L H K P N =>
      change
        some
          (RegularCauchyBinaryInterleavingUp.mk
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist S0))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist S1))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist E))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist O))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist T))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist R0))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist R1))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist L))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist H))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist K))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist P))
            (regularCauchyBinaryInterleavingDecodeBHist
              (regularCauchyBinaryInterleavingEncodeBHist N))) =
          some (RegularCauchyBinaryInterleavingUp.mk S0 S1 E O T R0 R1 L H K P N)
      rw [RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode S0,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode S1,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode E,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode O,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode T,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode R0,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode R1,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode L,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode H,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode K,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode P,
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyBinaryInterleavingUp} :
    regularCauchyBinaryInterleavingToEventFlow x =
      regularCauchyBinaryInterleavingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyBinaryInterleavingFromEventFlow
          (regularCauchyBinaryInterleavingToEventFlow x) =
        regularCauchyBinaryInterleavingFromEventFlow
          (regularCauchyBinaryInterleavingToEventFlow y) :=
    congrArg regularCauchyBinaryInterleavingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_fields
    (x y : RegularCauchyBinaryInterleavingUp) :
    regularCauchyBinaryInterleavingFields x =
      regularCauchyBinaryInterleavingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro hfields
  cases x with
  | mk S0a S1a Ea Oa Ta R0a R1a La Ha Ka Pa Na =>
      cases y with
      | mk S0b S1b Eb Ob Tb R0b R1b Lb Hb Kb Pb Nb =>
          cases hfields
          rfl

instance regularCauchyBinaryInterleavingBHistCarrier :
    BHistCarrier RegularCauchyBinaryInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyBinaryInterleavingToEventFlow
  fromEventFlow := regularCauchyBinaryInterleavingFromEventFlow

instance regularCauchyBinaryInterleavingChapterTasteGate :
    ChapterTasteGate RegularCauchyBinaryInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyBinaryInterleavingFromEventFlow
        (regularCauchyBinaryInterleavingToEventFlow x) = some x
    exact RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_injective heq)

instance regularCauchyBinaryInterleavingFieldFaithful :
    FieldFaithful RegularCauchyBinaryInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyBinaryInterleavingFields
  field_faithful := RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_fields

instance regularCauchyBinaryInterleavingNontrivial :
    Nontrivial RegularCauchyBinaryInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyBinaryInterleavingUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyBinaryInterleavingUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyBinaryInterleavingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyBinaryInterleavingChapterTasteGate

theorem RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyBinaryInterleavingDecodeBHist
        (regularCauchyBinaryInterleavingEncodeBHist h) = h) /\
      (forall x : RegularCauchyBinaryInterleavingUp,
        regularCauchyBinaryInterleavingFromEventFlow
          (regularCauchyBinaryInterleavingToEventFlow x) = some x) /\
        (forall x y : RegularCauchyBinaryInterleavingUp,
          regularCauchyBinaryInterleavingToEventFlow x =
            regularCauchyBinaryInterleavingToEventFlow y -> x = y) /\
          regularCauchyBinaryInterleavingEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_decode,
      RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyBinaryInterleavingTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

theorem RegularCauchyBinaryInterleavingNameCertObligations [AskSetup] [PackageSetup]
    {S0 S1 E O T R0 R1 L H K P N projectionRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyBinaryInterleavingFields
        (RegularCauchyBinaryInterleavingUp.mk S0 S1 E O T R0 R1 L H K P N) =
        [S0, S1, E, O, T, R0, R1, L, H, K, P, N] ->
      UnaryHistory S0 ->
        UnaryHistory E ->
          UnaryHistory T ->
            UnaryHistory R0 ->
              UnaryHistory R1 ->
                UnaryHistory L ->
                  Cont S0 E projectionRead ->
                    Cont projectionRead T toleranceRead ->
                      Cont toleranceRead L sealRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S0 ∨ hsame row S1 ∨ hsame row E ∨
                                    hsame row O ∨ hsame row T ∨ hsame row R0 ∨
                                      hsame row R1 ∨ hsame row L ∨ hsame row sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S0 E projectionRead ∧
                                    Cont projectionRead T toleranceRead ∧
                                      Cont toleranceRead L sealRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows s0Unary eUnary tUnary _r0Unary _r1Unary lUnary projectionRoute
    toleranceRoute sealRoute provenancePkg namePkg
  cases fieldRows
  have projectionUnary : UnaryHistory projectionRead :=
    unary_cont_closed s0Unary eUnary projectionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed projectionUnary tUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary lUnary sealRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, projectionRoute, toleranceRoute, sealRoute, provenancePkg, namePkg⟩
    }
  · exact sealUnary

end BEDC.Derived.RegularCauchyBinaryInterleavingUp

import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMeasureUp : Type where
  | mk (S E V A T R H C P N : BHist) : FiniteMeasureUp
  deriving DecidableEq

def finiteMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMeasureEncodeBHist h

def finiteMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMeasureDecodeBHist tail)

private theorem finiteMeasureDecode_encode_bhist :
    ∀ h : BHist, finiteMeasureDecodeBHist (finiteMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteMeasureToEventFlow : FiniteMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMeasureUp.mk S E V A T R H C P N =>
      [[BMark.b0],
        finiteMeasureEncodeBHist S,
        [BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteMeasureEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteMeasureEncodeBHist N]

def finiteMeasureFromEventFlow : EventFlow → Option FiniteMeasureUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: S :: _tag1 :: E :: _tag2 :: V :: _tag3 :: A :: _tag4 :: T :: _tag5 ::
      R :: _tag6 :: H :: _tag7 :: C :: _tag8 :: P :: _tag9 :: N :: [] =>
      some (FiniteMeasureUp.mk
        (finiteMeasureDecodeBHist S) (finiteMeasureDecodeBHist E)
        (finiteMeasureDecodeBHist V) (finiteMeasureDecodeBHist A)
        (finiteMeasureDecodeBHist T) (finiteMeasureDecodeBHist R)
        (finiteMeasureDecodeBHist H) (finiteMeasureDecodeBHist C)
        (finiteMeasureDecodeBHist P) (finiteMeasureDecodeBHist N))
  | _ => none

private theorem finiteMeasure_round_trip (x : FiniteMeasureUp) :
    finiteMeasureFromEventFlow (finiteMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S E V A T R H C P N =>
      change
        some
          (FiniteMeasureUp.mk
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist S))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist E))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist V))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist A))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist T))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist R))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist H))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist C))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist P))
            (finiteMeasureDecodeBHist (finiteMeasureEncodeBHist N))) =
          some (FiniteMeasureUp.mk S E V A T R H C P N)
      rw [finiteMeasureDecode_encode_bhist S]
      rw [finiteMeasureDecode_encode_bhist E]
      rw [finiteMeasureDecode_encode_bhist V]
      rw [finiteMeasureDecode_encode_bhist A]
      rw [finiteMeasureDecode_encode_bhist T]
      rw [finiteMeasureDecode_encode_bhist R]
      rw [finiteMeasureDecode_encode_bhist H]
      rw [finiteMeasureDecode_encode_bhist C]
      rw [finiteMeasureDecode_encode_bhist P]
      rw [finiteMeasureDecode_encode_bhist N]

private theorem finiteMeasureToEventFlow_injective {x y : FiniteMeasureUp} :
    finiteMeasureToEventFlow x = finiteMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteMeasureFromEventFlow (finiteMeasureToEventFlow x) =
        finiteMeasureFromEventFlow (finiteMeasureToEventFlow y) :=
    congrArg finiteMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteMeasure_round_trip x).symm
      (Eq.trans hread (finiteMeasure_round_trip y)))

def finiteMeasureFields : FiniteMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMeasureUp.mk S E V A T R H C P N => [S, E, V, A, T, R, H, C, P, N]

private theorem finiteMeasure_field_faithful :
    ∀ x y : FiniteMeasureUp, finiteMeasureFields x = finiteMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 E1 V1 A1 T1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 E2 V2 A2 T2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteMeasureBHistCarrier : BHistCarrier FiniteMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMeasureToEventFlow
  fromEventFlow := finiteMeasureFromEventFlow

instance finiteMeasureChapterTasteGate : ChapterTasteGate FiniteMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteMeasureFromEventFlow (finiteMeasureToEventFlow x) = some x
    exact finiteMeasure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteMeasureToEventFlow_injective heq)

instance finiteMeasureFieldFaithful : FieldFaithful FiniteMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteMeasureFields
  field_faithful := finiteMeasure_field_faithful

instance finiteMeasureNontrivial : Nontrivial FiniteMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro heq
        cases heq⟩

def taste_gate : ChapterTasteGate FiniteMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteMeasureChapterTasteGate

theorem FiniteMeasureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S E V A T R H C P N eventRead valueRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S E eventRead ->
      Cont V A valueRead ->
        Cont eventRead valueRead R ->
          PkgSig bundle R pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row R ∧
                  finiteMeasureFields (FiniteMeasureUp.mk S E V A T R H C P N) =
                    [S, E, V, A, T, R, H, C, P, N])
              (fun row : BHist =>
                hsame row S ∨ hsame row E ∨ hsame row V ∨ hsame row A ∨ hsame row T ∨
                  Cont S E eventRead ∨ Cont V A valueRead)
              (fun row : BHist => hsame row R ∧ PkgSig bundle R pkg)
              hsame ∧
              finiteMeasureFields (FiniteMeasureUp.mk S E V A T R H C P N) =
                [S, E, V, A, T, R, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro eventRoute valueRoute _readRoute pkgSig
  have fields_eq :
      finiteMeasureFields (FiniteMeasureUp.mk S E V A T R H C P N) =
        [S, E, V, A, T, R, H, C, P, N] := by
    rfl
  have sourceR :
      (fun row : BHist =>
        hsame row R ∧
          finiteMeasureFields (FiniteMeasureUp.mk S E V A T R H C P N) =
            [S, E, V, A, T, R, H, C, P, N]) R := by
    exact ⟨hsame_refl R, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            finiteMeasureFields (FiniteMeasureUp.mk S E V A T R H C P N) =
              [S, E, V, A, T, R, H, C, P, N])
        (fun row : BHist =>
          hsame row S ∨ hsame row E ∨ hsame row V ∨ hsame row A ∨ hsame row T ∨
            Cont S E eventRead ∨ Cont V A valueRead)
        (fun row : BHist => hsame row R ∧ PkgSig bundle R pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro R sourceR
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eventRoute)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, fields_eq⟩

end BEDC.Derived.FiniteMeasureUp

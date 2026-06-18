import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmpiricalRegularityPersistenceUp

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

inductive EmpiricalRegularityPersistenceUp : Type where
  | mk : (M R K L G A S F H C P N : BHist) → EmpiricalRegularityPersistenceUp
  deriving DecidableEq

def empiricalRegularityPersistenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: empiricalRegularityPersistenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: empiricalRegularityPersistenceEncodeBHist h

def empiricalRegularityPersistenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (empiricalRegularityPersistenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (empiricalRegularityPersistenceDecodeBHist tail)

private theorem empiricalRegularityPersistenceDecode_encode_bhist :
    ∀ h : BHist,
      empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def empiricalRegularityPersistenceFields :
    EmpiricalRegularityPersistenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N =>
      [M, R, K, L, G, A, S, F, H, C, P, N]

def empiricalRegularityPersistenceToEventFlow :
    EmpiricalRegularityPersistenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N =>
      [[BMark.b0],
        empiricalRegularityPersistenceEncodeBHist M,
        [BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        empiricalRegularityPersistenceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist N]

private def empiricalRegularityPersistenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      empiricalRegularityPersistenceEventAtDefault index rest

def empiricalRegularityPersistenceFromEventFlow
    (ef : EventFlow) : Option EmpiricalRegularityPersistenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EmpiricalRegularityPersistenceUp.mk
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 1 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 3 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 5 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 7 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 9 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 11 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 13 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 15 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 17 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 19 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 21 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 23 ef)))

private theorem empiricalRegularityPersistence_round_trip :
    ∀ x : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R K L G A S F H C P N =>
      change
        some
          (EmpiricalRegularityPersistenceUp.mk
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist M))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist R))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist K))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist L))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist G))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist A))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist S))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist F))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist H))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist C))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist P))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist N))) =
          some (EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N)
      rw [empiricalRegularityPersistenceDecode_encode_bhist M,
        empiricalRegularityPersistenceDecode_encode_bhist R,
        empiricalRegularityPersistenceDecode_encode_bhist K,
        empiricalRegularityPersistenceDecode_encode_bhist L,
        empiricalRegularityPersistenceDecode_encode_bhist G,
        empiricalRegularityPersistenceDecode_encode_bhist A,
        empiricalRegularityPersistenceDecode_encode_bhist S,
        empiricalRegularityPersistenceDecode_encode_bhist F,
        empiricalRegularityPersistenceDecode_encode_bhist H,
        empiricalRegularityPersistenceDecode_encode_bhist C,
        empiricalRegularityPersistenceDecode_encode_bhist P,
        empiricalRegularityPersistenceDecode_encode_bhist N]

private theorem empiricalRegularityPersistenceToEventFlow_injective
    {x y : EmpiricalRegularityPersistenceUp} :
    empiricalRegularityPersistenceToEventFlow x =
      empiricalRegularityPersistenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow x) =
        empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow y) :=
    congrArg empiricalRegularityPersistenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (empiricalRegularityPersistence_round_trip x).symm
      (Eq.trans hread (empiricalRegularityPersistence_round_trip y)))

private theorem empiricalRegularityPersistence_fields :
    ∀ x y : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFields x =
        empiricalRegularityPersistenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ R₁ K₁ L₁ G₁ A₁ S₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ R₂ K₂ L₂ G₂ A₂ S₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance empiricalRegularityPersistenceBHistCarrier :
    BHistCarrier EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := empiricalRegularityPersistenceToEventFlow
  fromEventFlow := empiricalRegularityPersistenceFromEventFlow

instance empiricalRegularityPersistenceChapterTasteGate :
    ChapterTasteGate EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x
    exact empiricalRegularityPersistence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (empiricalRegularityPersistenceToEventFlow_injective heq)

instance empiricalRegularityPersistenceFieldFaithful :
    FieldFaithful EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := empiricalRegularityPersistenceFields
  field_faithful := empiricalRegularityPersistence_fields

instance empiricalRegularityPersistenceNontrivial :
    Nontrivial EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmpiricalRegularityPersistenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      EmpiricalRegularityPersistenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EmpiricalRegularityPersistenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  empiricalRegularityPersistenceChapterTasteGate

theorem EmpiricalRegularityPersistenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEncodeBHist h) = h) ∧
      (∀ x : EmpiricalRegularityPersistenceUp,
        empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow x) = some x) ∧
        (∀ x y : EmpiricalRegularityPersistenceUp,
          empiricalRegularityPersistenceToEventFlow x =
            empiricalRegularityPersistenceToEventFlow y → x = y) ∧
          empiricalRegularityPersistenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨empiricalRegularityPersistenceDecode_encode_bhist,
      empiricalRegularityPersistence_round_trip,
      (by
        intro x y heq
        exact empiricalRegularityPersistenceToEventFlow_injective heq),
      rfl⟩

def EmpiricalRegularityPersistenceCarrier [AskSetup] [PackageSetup]
    (M R K L G A S F H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory R ∧ Cont M R K ∧ UnaryHistory L ∧ Cont K L G ∧
    UnaryHistory A ∧ Cont G A S ∧ UnaryHistory F ∧ Cont S F H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EmpiricalRegularityPersistenceCarrier_gap_exposure [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory K ∧ UnaryHistory L ∧
        UnaryHistory G ∧ UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont M R K ∧ Cont K L G ∧
            Cont G A S ∧ Cont S F H ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨mUnary, rUnary, mrk, lUnary, klg, aUnary, gas, fUnary, sfh, cUnary,
    pUnary, nUnary, pPkg, nPkg⟩ := carrier
  have kUnary : UnaryHistory K := unary_cont_closed mUnary rUnary mrk
  have gUnary : UnaryHistory G := unary_cont_closed kUnary lUnary klg
  have sUnary : UnaryHistory S := unary_cont_closed gUnary aUnary gas
  exact
    ⟨mUnary, rUnary, kUnary, lUnary, gUnary, sUnary, fUnary, cUnary, pUnary,
      nUnary, mrk, klg, gas, sfh, pPkg, nPkg⟩

theorem EmpiricalRegularityPersistenceCarrier_lawcertificate_consumption
    [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N lawRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      Cont A S lawRead ->
        PkgSig bundle lawRead pkg ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory K ∧ UnaryHistory L ∧
            UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory S ∧ UnaryHistory F ∧
              UnaryHistory lawRead ∧ Cont M R K ∧ Cont K L G ∧ Cont G A S ∧
                Cont A S lawRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle lawRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier lawRoute lawPkg
  obtain ⟨mUnary, rUnary, mrk, lUnary, klg, aUnary, gas, fUnary, _sfh, _cUnary,
    _pUnary, _nUnary, pPkg, _nPkg⟩ := carrier
  have kUnary : UnaryHistory K := unary_cont_closed mUnary rUnary mrk
  have gUnary : UnaryHistory G := unary_cont_closed kUnary lUnary klg
  have sUnary : UnaryHistory S := unary_cont_closed gUnary aUnary gas
  have lawUnary : UnaryHistory lawRead := unary_cont_closed aUnary sUnary lawRoute
  exact
    ⟨mUnary, rUnary, kUnary, lUnary, gUnary, aUnary, sUnary, fUnary, lawUnary,
      mrk, klg, gas, lawRoute, pPkg, lawPkg⟩

theorem EmpiricalRegularityPersistenceCarrier_nonescape [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N lawRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      Cont A S lawRead ->
        PkgSig bundle lawRead pkg ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory K ∧ UnaryHistory L ∧
            UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory S ∧ UnaryHistory F ∧
              UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                UnaryHistory lawRead ∧ Cont M R K ∧ Cont K L G ∧ Cont G A S ∧
                  Cont S F H ∧ Cont A S lawRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle lawRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier lawRoute lawPkg
  obtain ⟨mUnary, rUnary, mrk, lUnary, klg, aUnary, gas, fUnary, sfh, cUnary,
    pUnary, nUnary, pPkg, nPkg⟩ := carrier
  have kUnary : UnaryHistory K := unary_cont_closed mUnary rUnary mrk
  have gUnary : UnaryHistory G := unary_cont_closed kUnary lUnary klg
  have sUnary : UnaryHistory S := unary_cont_closed gUnary aUnary gas
  have hUnary : UnaryHistory H := unary_cont_closed sUnary fUnary sfh
  have lawUnary : UnaryHistory lawRead := unary_cont_closed aUnary sUnary lawRoute
  exact
    ⟨mUnary, rUnary, kUnary, lUnary, gUnary, aUnary, sUnary, fUnary, hUnary,
      cUnary, pUnary, nUnary, lawUnary, mrk, klg, gas, sfh, lawRoute, pPkg,
      nPkg, lawPkg⟩

theorem EmpiricalRegularityPersistenceCarrier_public_interface [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N lawRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      Cont A S lawRead -> Cont lawRead N publicRead -> PkgSig bundle lawRead pkg ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row M ∨ hsame row R ∨ hsame row K ∨ hsame row G ∨
                hsame row A ∨ hsame row S ∨ hsame row F ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row publicRead)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
            hsame ∧
            UnaryHistory publicRead ∧ Cont lawRead N publicRead ∧
              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier lawRoute publicRoute lawPkg publicPkg
  have nonescape :=
    EmpiricalRegularityPersistenceCarrier_nonescape
      (M := M) (R := R) (K := K) (L := L) (G := G) (A := A) (S := S)
      (F := F) (H := H) (C := C) (P := P) (N := N) (lawRead := lawRead)
      (bundle := bundle) (pkg := pkg) carrier lawRoute lawPkg
  obtain ⟨_mUnary, _rUnary, _kUnary, _lUnary, _gUnary, _aUnary, _sUnary,
    _fUnary, _hUnary, _cUnary, _pUnary, nUnary, lawUnary, _mrk, _klg, _gas,
    _sfh, _lawRoute, _pPkg, _nPkg, _lawPkg⟩ := nonescape
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lawUnary nUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row R ∨ hsame row K ∨ hsame row G ∨ hsame row A ∨
            hsame row S ∨ hsame row F ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row publicRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary, publicRoute, publicPkg⟩

end BEDC.Derived.EmpiricalRegularityPersistenceUp

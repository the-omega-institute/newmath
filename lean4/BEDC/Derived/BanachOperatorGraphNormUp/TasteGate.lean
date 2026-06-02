import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachOperatorGraphNormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachOperatorGraphNormUp : Type where
  | mk (X Y T Gamma A M Q L H C P N : BHist) : BanachOperatorGraphNormUp
  deriving DecidableEq

def banachOperatorGraphNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachOperatorGraphNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachOperatorGraphNormEncodeBHist h

def banachOperatorGraphNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachOperatorGraphNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachOperatorGraphNormDecodeBHist tail)

private theorem banachOperatorGraphNorm_decode_encode :
    ∀ h : BHist,
      banachOperatorGraphNormDecodeBHist
          (banachOperatorGraphNormEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachOperatorGraphNormFields :
    BanachOperatorGraphNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachOperatorGraphNormUp.mk X Y T Gamma A M Q L H C P N =>
      [X, Y, T, Gamma, A, M, Q, L, H, C, P, N]

def banachOperatorGraphNormToEventFlow :
    BanachOperatorGraphNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map banachOperatorGraphNormEncodeBHist
        (banachOperatorGraphNormFields x)

private def banachOperatorGraphNormRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachOperatorGraphNormRawAt index rest

def banachOperatorGraphNormFromEventFlow
    (flow : EventFlow) : Option BanachOperatorGraphNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachOperatorGraphNormUp.mk
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 0 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 1 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 2 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 3 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 4 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 5 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 6 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 7 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 8 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 9 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 10 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 11 flow)))

private theorem banachOperatorGraphNorm_round_trip :
    ∀ x : BanachOperatorGraphNormUp,
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T Gamma A M Q L H C P N =>
      change
        some
          (BanachOperatorGraphNormUp.mk
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist X))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Y))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist T))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Gamma))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist A))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist M))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Q))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist L))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist H))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist C))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist P))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist N))) =
          some (BanachOperatorGraphNormUp.mk X Y T Gamma A M Q L H C P N)
      rw [banachOperatorGraphNorm_decode_encode X,
        banachOperatorGraphNorm_decode_encode Y,
        banachOperatorGraphNorm_decode_encode T,
        banachOperatorGraphNorm_decode_encode Gamma,
        banachOperatorGraphNorm_decode_encode A,
        banachOperatorGraphNorm_decode_encode M,
        banachOperatorGraphNorm_decode_encode Q,
        banachOperatorGraphNorm_decode_encode L,
        banachOperatorGraphNorm_decode_encode H,
        banachOperatorGraphNorm_decode_encode C,
        banachOperatorGraphNorm_decode_encode P,
        banachOperatorGraphNorm_decode_encode N]

private theorem banachOperatorGraphNormToEventFlow_injective
    {x y : BanachOperatorGraphNormUp} :
    banachOperatorGraphNormToEventFlow x =
        banachOperatorGraphNormToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow y) :=
    congrArg banachOperatorGraphNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (banachOperatorGraphNorm_round_trip x).symm
      (Eq.trans hread (banachOperatorGraphNorm_round_trip y)))

private theorem banachOperatorGraphNorm_field_faithful :
    ∀ x y : BanachOperatorGraphNormUp,
      banachOperatorGraphNormFields x = banachOperatorGraphNormFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ T₁ Gamma₁ A₁ M₁ Q₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ T₂ Gamma₂ A₂ M₂ Q₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hY tail1
          injection tail1 with hT tail2
          injection tail2 with hGamma tail3
          injection tail3 with hA tail4
          injection tail4 with hM tail5
          injection tail5 with hQ tail6
          injection tail6 with hL tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hX
          subst hY
          subst hT
          subst hGamma
          subst hA
          subst hM
          subst hQ
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance banachOperatorGraphNormBHistCarrier :
    BHistCarrier BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachOperatorGraphNormToEventFlow
  fromEventFlow := banachOperatorGraphNormFromEventFlow

instance banachOperatorGraphNormChapterTasteGate :
    ChapterTasteGate BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        some x
    exact banachOperatorGraphNorm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachOperatorGraphNormToEventFlow_injective heq)

instance banachOperatorGraphNormFieldFaithful :
    FieldFaithful BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachOperatorGraphNormFields
  field_faithful := banachOperatorGraphNorm_field_faithful

instance banachOperatorGraphNormNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachOperatorGraphNormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BanachOperatorGraphNormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachOperatorGraphNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachOperatorGraphNormChapterTasteGate

theorem BanachOperatorGraphNormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BanachOperatorGraphNormUp) ∧
      Nonempty (FieldFaithful BanachOperatorGraphNormUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BanachOperatorGraphNormUp) ∧
          (∀ h : BHist,
            banachOperatorGraphNormDecodeBHist
                (banachOperatorGraphNormEncodeBHist h) =
              h) ∧
            (∀ x : BanachOperatorGraphNormUp,
              banachOperatorGraphNormFromEventFlow
                  (banachOperatorGraphNormToEventFlow x) =
                some x) ∧
              banachOperatorGraphNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro banachOperatorGraphNormChapterTasteGate,
      Nonempty.intro banachOperatorGraphNormFieldFaithful,
      Nonempty.intro banachOperatorGraphNormNontrivial,
      banachOperatorGraphNorm_decode_encode,
      banachOperatorGraphNorm_round_trip,
      rfl⟩

end BEDC.Derived.BanachOperatorGraphNormUp.TasteGate

namespace BEDC.Derived.BanachOperatorGraphNormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BanachOperatorGraphNormCarrier [AskSetup] [PackageSetup]
    (X Y T Gamma A M Q L H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory T ∧ UnaryHistory Gamma ∧
    UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory L ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BanachOperatorGraphNormCompletionHandoff
    [AskSetup] [PackageSetup]
    {X Y T Gamma A M Q L H C P N graphRead normRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory Gamma ->
        UnaryHistory M ->
          UnaryHistory Q ->
            UnaryHistory L ->
              Cont X Gamma graphRead ->
                Cont M Q normRead ->
                  Cont L normRead completionRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row Y ∨ hsame row T ∨
                              hsame row Gamma ∨ hsame row A ∨ hsame row M ∨
                                hsame row Q ∨ hsame row L ∨ hsame row completionRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                          hsame ∧
                        UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryX unaryGamma unaryM unaryQ unaryL graphRoute normRoute completionRoute pkgSig
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed unaryX unaryGamma graphRoute
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed unaryM unaryQ normRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed unaryL normReadUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row T ∨ hsame row Gamma ∨
              hsame row A ∨ hsame row M ∨ hsame row Q ∨ hsame row L ∨
                hsame row completionRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          ⟨hsame_refl completionRead,
            unary_transport completionReadUnary (hsame_refl completionRead)⟩
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
      exact ⟨source.right, pkgSig⟩
  }
  have _graphNormConsumerRead : UnaryHistory graphRead := graphReadUnary
  exact ⟨cert, completionReadUnary⟩

theorem BanachOperatorGraphNormCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {X Y T Gamma A M Q L H C P N graphRead normRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory Y ->
        UnaryHistory T ->
          UnaryHistory Gamma ->
            UnaryHistory A ->
              UnaryHistory M ->
                UnaryHistory Q ->
                  UnaryHistory L ->
                    Cont X Gamma graphRead ->
                      Cont M Q normRead ->
                        Cont L normRead completionRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  Cont X Gamma graphRead ∧ Cont M Q normRead ∧
                                    Cont L normRead completionRead)
                                (fun row : BHist =>
                                  hsame row completionRead ∧ PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory graphRead ∧ UnaryHistory normRead ∧
                                UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryX _unaryY _unaryT unaryGamma _unaryA unaryM unaryQ unaryL graphRoute
    normRoute completionRoute pkgSig
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed unaryX unaryGamma graphRoute
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed unaryM unaryQ normRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed unaryL normReadUnary completionRoute
  have source :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        completionRead := by
    exact ⟨hsame_refl completionRead, completionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont X Gamma graphRead ∧ Cont M Q normRead ∧
              Cont L normRead completionRead)
          (fun row : BHist => hsame row completionRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead source
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row _sourceRow
      exact ⟨graphRoute, normRoute, completionRoute⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, pkgSig⟩
  }
  exact ⟨cert, graphReadUnary, normReadUnary, completionReadUnary⟩

theorem BanachOperatorGraphNorm_no_quotient_graph [AskSetup] [PackageSetup]
    {X Y T Gamma A M Q L H C P N graphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachOperatorGraphNormCarrier X Y T Gamma A M Q L H C P N bundle pkg ->
      Cont Gamma A graphRead ->
        PkgSig bundle N pkg ->
          UnaryHistory Gamma ∧ UnaryHistory A ∧ UnaryHistory graphRead ∧
            Cont Gamma A graphRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier graphRoute localNamePkg
  obtain ⟨_xUnary, _yUnary, _tUnary, gammaUnary, aUnary, _mUnary, _qUnary, _lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, provenancePkg, _carrierLocalPkg⟩ := carrier
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed gammaUnary aUnary graphRoute
  exact ⟨gammaUnary, aUnary, graphUnary, graphRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.BanachOperatorGraphNormUp

import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformHomeomorphismUp

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

inductive CompactUniformHomeomorphismUp : Type where
  | mk (X Y M T F G A B E S Q R H C P N : BHist) : CompactUniformHomeomorphismUp
  deriving DecidableEq

def compactUniformHomeomorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformHomeomorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformHomeomorphismEncodeBHist h

def compactUniformHomeomorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformHomeomorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformHomeomorphismDecodeBHist tail)

private theorem compactUniformHomeomorphism_decode_encode_bhist :
    ∀ h : BHist,
      compactUniformHomeomorphismDecodeBHist
        (compactUniformHomeomorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformHomeomorphismFields : CompactUniformHomeomorphismUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformHomeomorphismUp.mk X Y M T F G A B E S Q R H C P N =>
      [X, Y, M, T, F, G, A, B, E, S, Q, R, H, C, P, N]

def compactUniformHomeomorphismToEventFlow : CompactUniformHomeomorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformHomeomorphismFields x).map compactUniformHomeomorphismEncodeBHist

private def compactUniformHomeomorphismEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformHomeomorphismEventAt index rest

def compactUniformHomeomorphismFromEventFlow
    (ef : EventFlow) : Option CompactUniformHomeomorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformHomeomorphismUp.mk
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 0 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 1 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 2 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 3 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 4 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 5 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 6 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 7 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 8 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 9 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 10 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 11 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 12 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 13 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 14 ef))
      (compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEventAt 15 ef)))

private theorem compactUniformHomeomorphism_round_trip
    (x : CompactUniformHomeomorphismUp) :
    compactUniformHomeomorphismFromEventFlow
        (compactUniformHomeomorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y M T F G A B E S Q R H C P N =>
      change
        some
          (CompactUniformHomeomorphismUp.mk
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist X))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist Y))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist M))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist T))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist F))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist G))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist A))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist B))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist E))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist S))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist Q))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist R))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist H))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist C))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist P))
            (compactUniformHomeomorphismDecodeBHist
              (compactUniformHomeomorphismEncodeBHist N))) =
          some (CompactUniformHomeomorphismUp.mk X Y M T F G A B E S Q R H C P N)
      rw [compactUniformHomeomorphism_decode_encode_bhist X,
        compactUniformHomeomorphism_decode_encode_bhist Y,
        compactUniformHomeomorphism_decode_encode_bhist M,
        compactUniformHomeomorphism_decode_encode_bhist T,
        compactUniformHomeomorphism_decode_encode_bhist F,
        compactUniformHomeomorphism_decode_encode_bhist G,
        compactUniformHomeomorphism_decode_encode_bhist A,
        compactUniformHomeomorphism_decode_encode_bhist B,
        compactUniformHomeomorphism_decode_encode_bhist E,
        compactUniformHomeomorphism_decode_encode_bhist S,
        compactUniformHomeomorphism_decode_encode_bhist Q,
        compactUniformHomeomorphism_decode_encode_bhist R,
        compactUniformHomeomorphism_decode_encode_bhist H,
        compactUniformHomeomorphism_decode_encode_bhist C,
        compactUniformHomeomorphism_decode_encode_bhist P,
        compactUniformHomeomorphism_decode_encode_bhist N]

private theorem compactUniformHomeomorphismToEventFlow_injective
    {x y : CompactUniformHomeomorphismUp} :
    compactUniformHomeomorphismToEventFlow x =
      compactUniformHomeomorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformHomeomorphismFromEventFlow (compactUniformHomeomorphismToEventFlow x) =
        compactUniformHomeomorphismFromEventFlow (compactUniformHomeomorphismToEventFlow y) :=
    congrArg compactUniformHomeomorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformHomeomorphism_round_trip x).symm
      (Eq.trans hread (compactUniformHomeomorphism_round_trip y)))

instance compactUniformHomeomorphismBHistCarrier :
    BHistCarrier CompactUniformHomeomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformHomeomorphismToEventFlow
  fromEventFlow := compactUniformHomeomorphismFromEventFlow

instance compactUniformHomeomorphismChapterTasteGate :
    ChapterTasteGate CompactUniformHomeomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformHomeomorphismFromEventFlow (compactUniformHomeomorphismToEventFlow x) =
        some x
    exact compactUniformHomeomorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformHomeomorphismToEventFlow_injective heq)

theorem CompactUniformHomeomorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformHomeomorphismDecodeBHist (compactUniformHomeomorphismEncodeBHist h) =
        h) ∧
      (∀ x : CompactUniformHomeomorphismUp,
        compactUniformHomeomorphismFromEventFlow
          (compactUniformHomeomorphismToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformHomeomorphismUp,
          compactUniformHomeomorphismToEventFlow x =
            compactUniformHomeomorphismToEventFlow y → x = y) ∧
          compactUniformHomeomorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactUniformHomeomorphism_decode_encode_bhist,
      compactUniformHomeomorphism_round_trip,
      (fun _ _ heq => compactUniformHomeomorphismToEventFlow_injective heq),
      rfl⟩

def CompactUniformHomeomorphismCarrier [AskSetup] [PackageSetup]
    (X Y M T F G A B E S Q R H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory M ∧ UnaryHistory T ∧
    UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory B ∧
      UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory R ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CompactUniformHomeomorphismNameCertSurface [AskSetup] [PackageSetup]
    {X Y M T F G A B E S Q R H C P N finiteNet graphRead separatedRead modulusRead
      realSeal localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformHomeomorphismCarrier X Y M T F G A B E S Q R H C P N bundle pkg ->
      Cont M T finiteNet ->
        Cont F G graphRead ->
          Cont graphRead B separatedRead ->
            Cont separatedRead E modulusRead ->
              Cont Q R realSeal ->
                Cont H C localRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle localRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row Y ∨ hsame row M ∨
                              hsame row T ∨ hsame row F ∨ hsame row G ∨
                                hsame row A ∨ hsame row B ∨ hsame row E ∨
                                  hsame row finiteNet ∨ hsame row graphRead ∨
                                    hsame row separatedRead ∨ hsame row modulusRead ∨
                                      hsame row localRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M T finiteNet ∧
                              Cont F G graphRead ∧ Cont graphRead B separatedRead ∧
                                Cont separatedRead E modulusRead ∧ Cont H C localRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
                          hsame ∧
                        UnaryHistory finiteNet ∧ UnaryHistory graphRead ∧
                          UnaryHistory separatedRead ∧ UnaryHistory modulusRead ∧
                            UnaryHistory realSeal ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: CompactUniformHomeomorphismCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier finiteNetRoute graphRoute separatedRoute modulusRoute realRoute localRoute
    provenancePkg localPkg
  obtain ⟨_unaryX, _unaryY, unaryM, unaryT, unaryF, unaryG, _unaryA, unaryB, unaryE,
    _unaryS, unaryQ, unaryR, unaryH, unaryC, _unaryP, _unaryN, _carrierPkgP,
    _carrierPkgN⟩ := carrier
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed unaryM unaryT finiteNetRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed unaryF unaryG graphRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed graphUnary unaryB separatedRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed separatedUnary unaryE modulusRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed unaryQ unaryR realRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed unaryH unaryC localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row M ∨ hsame row T ∨
              hsame row F ∨ hsame row G ∨ hsame row A ∨ hsame row B ∨
                hsame row E ∨ hsame row finiteNet ∨ hsame row graphRead ∨
                  hsame row separatedRead ∨ hsame row modulusRead ∨
                    hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M T finiteNet ∧ Cont F G graphRead ∧
              Cont graphRead B separatedRead ∧ Cont separatedRead E modulusRead ∧
                Cont H C localRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead ⟨hsame_refl modulusRead, modulusUnary⟩
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
        cases sameRows
        exact source
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, finiteNetRoute, graphRoute, separatedRoute, modulusRoute,
          localRoute, provenancePkg, localPkg⟩
  }
  exact
    ⟨cert, finiteNetUnary, graphUnary, separatedUnary, modulusUnary, realSealUnary,
      localUnary⟩

end BEDC.Derived.CompactUniformHomeomorphismUp

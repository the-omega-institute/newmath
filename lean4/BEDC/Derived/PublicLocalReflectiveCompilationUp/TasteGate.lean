import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PublicLocalReflectiveCompilationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PublicLocalReflectiveCompilationUp : Type where
  | mk (A M C S L U X F T E H K P N : BHist) : PublicLocalReflectiveCompilationUp
  deriving DecidableEq

def publicLocalReflectiveCompilationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: publicLocalReflectiveCompilationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: publicLocalReflectiveCompilationEncodeBHist h

def publicLocalReflectiveCompilationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (publicLocalReflectiveCompilationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (publicLocalReflectiveCompilationDecodeBHist tail)

private theorem PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      publicLocalReflectiveCompilationDecodeBHist
        (publicLocalReflectiveCompilationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem publicLocalReflectiveCompilationEncodeBHist_injective
    {h k : BHist} :
    publicLocalReflectiveCompilationEncodeBHist h =
      publicLocalReflectiveCompilationEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  exact
    Eq.trans
      (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode h).symm
      (Eq.trans (congrArg publicLocalReflectiveCompilationDecodeBHist heq)
        (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode k))

private theorem publicLocalReflectiveCompilation_mk_congr
    {A A' M M' C C' S S' L L' U U' X X' F F' T T' E E' H H' K K' P P' N N' :
      BHist}
    (hA : A' = A) (hM : M' = M) (hC : C' = C) (hS : S' = S)
    (hL : L' = L) (hU : U' = U) (hX : X' = X) (hF : F' = F)
    (hT : T' = T) (hE : E' = E) (hH : H' = H) (hK : K' = K)
    (hP : P' = P) (hN : N' = N) :
    PublicLocalReflectiveCompilationUp.mk A' M' C' S' L' U' X' F' T' E' H' K' P' N' =
      PublicLocalReflectiveCompilationUp.mk A M C S L U X F T E H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hM
  cases hC
  cases hS
  cases hL
  cases hU
  cases hX
  cases hF
  cases hT
  cases hE
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def publicLocalReflectiveCompilationFields :
    PublicLocalReflectiveCompilationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PublicLocalReflectiveCompilationUp.mk A M C S L U X F T E H K P N =>
      [A, M, C, S, L, U, X, F, T, E, H, K, P, N]

def publicLocalReflectiveCompilationToEventFlow :
    PublicLocalReflectiveCompilationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PublicLocalReflectiveCompilationUp.mk A M C S L U X F T E H K P N =>
      [publicLocalReflectiveCompilationEncodeBHist A,
        publicLocalReflectiveCompilationEncodeBHist M,
        publicLocalReflectiveCompilationEncodeBHist C,
        publicLocalReflectiveCompilationEncodeBHist S,
        publicLocalReflectiveCompilationEncodeBHist L,
        publicLocalReflectiveCompilationEncodeBHist U,
        publicLocalReflectiveCompilationEncodeBHist X,
        publicLocalReflectiveCompilationEncodeBHist F,
        publicLocalReflectiveCompilationEncodeBHist T,
        publicLocalReflectiveCompilationEncodeBHist E,
        publicLocalReflectiveCompilationEncodeBHist H,
        publicLocalReflectiveCompilationEncodeBHist K,
        publicLocalReflectiveCompilationEncodeBHist P,
        publicLocalReflectiveCompilationEncodeBHist N]

def publicLocalReflectiveCompilationFromEventFlow :
    EventFlow → Option PublicLocalReflectiveCompilationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | U :: rest5 =>
                          match rest5 with
                          | [] => none
                          | X :: rest6 =>
                              match rest6 with
                              | [] => none
                              | F :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | T :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | H :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | K :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | P :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (PublicLocalReflectiveCompilationUp.mk
                                                                  (publicLocalReflectiveCompilationDecodeBHist A)
                                                                  (publicLocalReflectiveCompilationDecodeBHist M)
                                                                  (publicLocalReflectiveCompilationDecodeBHist C)
                                                                  (publicLocalReflectiveCompilationDecodeBHist S)
                                                                  (publicLocalReflectiveCompilationDecodeBHist L)
                                                                  (publicLocalReflectiveCompilationDecodeBHist U)
                                                                  (publicLocalReflectiveCompilationDecodeBHist X)
                                                                  (publicLocalReflectiveCompilationDecodeBHist F)
                                                                  (publicLocalReflectiveCompilationDecodeBHist T)
                                                                  (publicLocalReflectiveCompilationDecodeBHist E)
                                                                  (publicLocalReflectiveCompilationDecodeBHist H)
                                                                  (publicLocalReflectiveCompilationDecodeBHist K)
                                                                  (publicLocalReflectiveCompilationDecodeBHist P)
                                                                  (publicLocalReflectiveCompilationDecodeBHist N))
                                                          | _ :: _ => none

private theorem PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PublicLocalReflectiveCompilationUp,
      publicLocalReflectiveCompilationFromEventFlow
        (publicLocalReflectiveCompilationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M C S L U X F T E H K P N =>
      exact
        congrArg some
          (publicLocalReflectiveCompilation_mk_congr
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode A)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode M)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode C)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode S)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode L)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode U)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode X)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode F)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode T)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode E)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode H)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode K)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode P)
            (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode N))

private theorem publicLocalReflectiveCompilationToEventFlow_injective
    {x y : PublicLocalReflectiveCompilationUp} :
    publicLocalReflectiveCompilationToEventFlow x =
      publicLocalReflectiveCompilationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      publicLocalReflectiveCompilationFromEventFlow
          (publicLocalReflectiveCompilationToEventFlow x) =
        publicLocalReflectiveCompilationFromEventFlow
          (publicLocalReflectiveCompilationToEventFlow y) :=
    congrArg publicLocalReflectiveCompilationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_round_trip y)))

private theorem PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_fields :
    ∀ x y : PublicLocalReflectiveCompilationUp,
      publicLocalReflectiveCompilationFields x =
        publicLocalReflectiveCompilationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ M₁ C₁ S₁ L₁ U₁ X₁ F₁ T₁ E₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk A₂ M₂ C₂ S₂ L₂ U₂ X₂ F₂ T₂ E₂ H₂ K₂ P₂ N₂ =>
          injection hfields with hA tail0
          injection tail0 with hM tail1
          injection tail1 with hC tail2
          injection tail2 with hS tail3
          injection tail3 with hL tail4
          injection tail4 with hU tail5
          injection tail5 with hX tail6
          injection tail6 with hF tail7
          injection tail7 with hT tail8
          injection tail8 with hE tail9
          injection tail9 with hH tail10
          injection tail10 with hK tail11
          injection tail11 with hP tail12
          injection tail12 with hN _
          subst hA
          subst hM
          subst hC
          subst hS
          subst hL
          subst hU
          subst hX
          subst hF
          subst hT
          subst hE
          subst hH
          subst hK
          subst hP
          subst hN
          rfl

instance publicLocalReflectiveCompilationBHistCarrier :
    BHistCarrier PublicLocalReflectiveCompilationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := publicLocalReflectiveCompilationToEventFlow
  fromEventFlow := publicLocalReflectiveCompilationFromEventFlow

instance publicLocalReflectiveCompilationChapterTasteGate :
    ChapterTasteGate PublicLocalReflectiveCompilationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      publicLocalReflectiveCompilationFromEventFlow
        (publicLocalReflectiveCompilationToEventFlow x) = some x
    exact PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (publicLocalReflectiveCompilationToEventFlow_injective heq)

instance publicLocalReflectiveCompilationFieldFaithful :
    FieldFaithful PublicLocalReflectiveCompilationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := publicLocalReflectiveCompilationFields
  field_faithful := PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_fields

instance publicLocalReflectiveCompilationNontrivial :
    Nontrivial PublicLocalReflectiveCompilationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PublicLocalReflectiveCompilationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PublicLocalReflectiveCompilationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PublicLocalReflectiveCompilationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  publicLocalReflectiveCompilationChapterTasteGate

theorem PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      publicLocalReflectiveCompilationDecodeBHist
        (publicLocalReflectiveCompilationEncodeBHist h) = h) ∧
      (∀ x : PublicLocalReflectiveCompilationUp,
        publicLocalReflectiveCompilationFromEventFlow
          (publicLocalReflectiveCompilationToEventFlow x) = some x) ∧
      (∀ x y : PublicLocalReflectiveCompilationUp,
        publicLocalReflectiveCompilationToEventFlow x =
          publicLocalReflectiveCompilationToEventFlow y → x = y) ∧
      publicLocalReflectiveCompilationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode
  constructor
  · intro x
    cases x with
    | mk A M C S L U X F T E H K P N =>
        exact
          congrArg some
            (publicLocalReflectiveCompilation_mk_congr
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode A)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode M)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode C)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode S)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode L)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode U)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode X)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode F)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode T)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode E)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode H)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode K)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode P)
              (PublicLocalReflectiveCompilationTasteGate_single_carrier_alignment_decode N))
  constructor
  · intro x y heq
    cases x with
    | mk A₁ M₁ C₁ S₁ L₁ U₁ X₁ F₁ T₁ E₁ H₁ K₁ P₁ N₁ =>
        cases y with
        | mk A₂ M₂ C₂ S₂ L₂ U₂ X₂ F₂ T₂ E₂ H₂ K₂ P₂ N₂ =>
            injection heq with hA tail0
            injection tail0 with hM tail1
            injection tail1 with hC tail2
            injection tail2 with hS tail3
            injection tail3 with hL tail4
            injection tail4 with hU tail5
            injection tail5 with hX tail6
            injection tail6 with hF tail7
            injection tail7 with hT tail8
            injection tail8 with hE tail9
            injection tail9 with hH tail10
            injection tail10 with hK tail11
            injection tail11 with hP tail12
            injection tail12 with hN _
            exact
              publicLocalReflectiveCompilation_mk_congr
                (publicLocalReflectiveCompilationEncodeBHist_injective hA)
                (publicLocalReflectiveCompilationEncodeBHist_injective hM)
                (publicLocalReflectiveCompilationEncodeBHist_injective hC)
                (publicLocalReflectiveCompilationEncodeBHist_injective hS)
                (publicLocalReflectiveCompilationEncodeBHist_injective hL)
                (publicLocalReflectiveCompilationEncodeBHist_injective hU)
                (publicLocalReflectiveCompilationEncodeBHist_injective hX)
                (publicLocalReflectiveCompilationEncodeBHist_injective hF)
                (publicLocalReflectiveCompilationEncodeBHist_injective hT)
                (publicLocalReflectiveCompilationEncodeBHist_injective hE)
                (publicLocalReflectiveCompilationEncodeBHist_injective hH)
                (publicLocalReflectiveCompilationEncodeBHist_injective hK)
                (publicLocalReflectiveCompilationEncodeBHist_injective hP)
                (publicLocalReflectiveCompilationEncodeBHist_injective hN)
  · rfl

end BEDC.Derived.PublicLocalReflectiveCompilationUp

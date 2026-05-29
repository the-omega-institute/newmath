import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalExpansionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalExpansionUp : Type where
  | mk (D W V Q R E H C P N : BHist) : DecimalExpansionUp
  deriving DecidableEq

def DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h

def DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DecimalExpansionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist
          (DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DecimalExpansionTasteGate_single_carrier_alignment_fields :
    DecimalExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalExpansionUp.mk D W V Q R E H C P N => [D, W, V, Q, R, E, H, C, P, N]

def DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow :
    DecimalExpansionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (DecimalExpansionTasteGate_single_carrier_alignment_fields x).map
      DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist

def DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DecimalExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | D :: W :: V :: Q :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (DecimalExpansionUp.mk
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist D)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist W)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist V)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist Q)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist R)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist E)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist H)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist C)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist P)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem DecimalExpansionTasteGate_single_carrier_alignment_round_trip :
    forall x : DecimalExpansionUp,
      DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
          (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W V Q R E H C P N =>
      simp only [DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow,
        DecimalExpansionTasteGate_single_carrier_alignment_fields,
        DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DecimalExpansionTasteGate_single_carrier_alignment_decode_encode]

private theorem DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DecimalExpansionUp} :
    DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x =
        DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
            (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) :=
        (DecimalExpansionTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
            (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := DecimalExpansionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance DecimalExpansionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow

instance DecimalExpansionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
          (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DecimalExpansionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DecimalExpansionTasteGate_single_carrier_alignment :
    (forall D W V Q R E H C P N : BHist,
      DecimalExpansionTasteGate_single_carrier_alignment_fields
          (DecimalExpansionUp.mk D W V Q R E H C P N) =
        [D, W, V, Q, R, E, H, C, P, N]) ∧
      DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.DecimalExpansionUp.TasteGate

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DecimalExpansionDigitLedgerInjection {D W V Q route : BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory Q ->
          Cont D W V -> Cont V Q route -> UnaryHistory V ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary qUnary digitWindow placeComparison
  have placeUnary : UnaryHistory V :=
    unary_cont_closed dUnary wUnary digitWindow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed placeUnary qUnary placeComparison
  exact ⟨placeUnary, routeUnary⟩

theorem DecimalExpansionEndpointNormalizationHandoff
    {D W V Q R E «prefix» comparison handoff «seal» : BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              Cont D W «prefix» ->
                Cont «prefix» V comparison ->
                  Cont comparison Q handoff ->
                    Cont handoff R «seal» ->
                      UnaryHistory «prefix» ∧
                        UnaryHistory comparison ∧ UnaryHistory handoff ∧ UnaryHistory «seal» := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary digitWindow prefixPlace comparisonDyadic handoffRat
  have prefixUnary : UnaryHistory «prefix» :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonDyadic
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary rUnary handoffRat
  exact ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary⟩

theorem DecimalExpansionDigitWindowObligations
    {D W V Q R E H C P N digitWindow placeValue dyadic regseq realSeal transport replay
      provenance nameRoute : BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont D W digitWindow ->
                          Cont digitWindow V placeValue ->
                            Cont placeValue Q dyadic ->
                              Cont dyadic R regseq ->
                                Cont regseq E realSeal ->
                                  Cont realSeal H transport ->
                                    Cont transport C replay ->
                                      Cont replay P provenance ->
                                        Cont provenance N nameRoute ->
                                          UnaryHistory digitWindow ∧
                                            UnaryHistory placeValue ∧
                                              UnaryHistory dyadic ∧
                                                UnaryHistory regseq ∧
                                                  UnaryHistory realSeal ∧
                                                    UnaryHistory transport ∧
                                                      UnaryHistory replay ∧
                                                        UnaryHistory provenance ∧
                                                          UnaryHistory nameRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro digitUnary windowUnary valueUnary dyadicUnary regseqUnary realUnary transportUnary
    replayUnary provenanceUnary nameUnary digitWindowCont placeValueCont dyadicCont
    regseqCont realSealCont transportCont replayCont provenanceCont nameCont
  have digitWindowUnary : UnaryHistory digitWindow :=
    unary_cont_closed digitUnary windowUnary digitWindowCont
  have placeValueUnary : UnaryHistory placeValue :=
    unary_cont_closed digitWindowUnary valueUnary placeValueCont
  have dyadicClosed : UnaryHistory dyadic :=
    unary_cont_closed placeValueUnary dyadicUnary dyadicCont
  have regseqClosed : UnaryHistory regseq :=
    unary_cont_closed dyadicClosed regseqUnary regseqCont
  have realSealClosed : UnaryHistory realSeal :=
    unary_cont_closed regseqClosed realUnary realSealCont
  have transportClosed : UnaryHistory transport :=
    unary_cont_closed realSealClosed transportUnary transportCont
  have replayClosed : UnaryHistory replay :=
    unary_cont_closed transportClosed replayUnary replayCont
  have provenanceClosed : UnaryHistory provenance :=
    unary_cont_closed replayClosed provenanceUnary provenanceCont
  have nameClosed : UnaryHistory nameRoute :=
    unary_cont_closed provenanceClosed nameUnary nameCont
  exact
    ⟨digitWindowUnary, placeValueUnary, dyadicClosed, regseqClosed, realSealClosed,
      transportClosed, replayClosed, provenanceClosed, nameClosed⟩

end BEDC.Derived.DecimalExpansionUp

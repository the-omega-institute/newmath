import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Cancellation
import BEDC.Derived.GroupUp
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.ProbSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.PreorderUp

def ProbSpacePublicEventPacket (omega one event complement sum : BHist) : Prop :=
  UnaryHistory event ∧
    UnaryHistory complement ∧
      Cont event complement sum ∧
        hsame omega one ∧
          hsame omega sum

theorem ProbSpaceComplementMass_additive_readback {omega one event complement sum : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> hsame sum one ∧ UnaryHistory sum := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  exact And.intro (hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne)
    (unary_cont_closed eventCarrier complementCarrier sumRel)

theorem ProbSpacePublicEventPacket_normalization_bounds {omega one event complement sum : BHist} :
    ProbSpacePublicEventPacket omega one event complement sum ->
      hsame sum one ∧ UnaryHistory sum ∧ Cont event complement sum ∧
        PreorderPrefixLE event one := by
  intro packet
  have readback : hsame sum one ∧ UnaryHistory sum :=
    ProbSpaceComplementMass_additive_readback packet.left packet.right.left
      packet.right.right.left packet.right.right.right.right packet.right.right.right.left
  have eventSum : PreorderPrefixLE event sum :=
    Exists.intro complement (And.intro packet.right.left packet.right.right.left)
  have sumOne : PreorderPrefixLE sum one :=
    PreorderPrefixLE_of_hsame readback.left
  exact And.intro readback.left
    (And.intro readback.right
      (And.intro packet.right.right.left (PreorderPrefixLE_trans eventSum sumOne)))

theorem ProbSpacePublicEventPacket_transport_rows
    {omega one omega' one' event event' complement complement' sum sum' : BHist} :
    hsame omega omega' -> hsame one one' -> hsame event event' ->
      hsame complement complement' -> hsame sum sum' ->
        ProbSpacePublicEventPacket omega one event complement sum ->
          ProbSpacePublicEventPacket omega' one' event' complement' sum' ∧
            UnaryHistory event' ∧ UnaryHistory complement' ∧ Cont event' complement' sum' ∧
              hsame omega' one' ∧ hsame omega' sum' := by
  intro sameOmega sameOne sameEvent sameComplement sameSum packet
  have eventUnary : UnaryHistory event' :=
    unary_transport packet.left sameEvent
  have complementUnary : UnaryHistory complement' :=
    unary_transport packet.right.left sameComplement
  have transportedCont : Cont event' complement' sum' :=
    cont_hsame_transport sameEvent sameComplement sameSum packet.right.right.left
  have omegaOne : hsame omega' one' :=
    hsame_trans (hsame_symm sameOmega)
      (hsame_trans packet.right.right.right.left sameOne)
  have omegaSum : hsame omega' sum' :=
    hsame_trans (hsame_symm sameOmega)
      (hsame_trans packet.right.right.right.right sameSum)
  have transportedPacket :
      ProbSpacePublicEventPacket omega' one' event' complement' sum' :=
    And.intro eventUnary
      (And.intro complementUnary (And.intro transportedCont (And.intro omegaOne omegaSum)))
  exact And.intro transportedPacket
    (And.intro eventUnary
      (And.intro complementUnary (And.intro transportedCont (And.intro omegaOne omegaSum))))

theorem ProbSpaceComplementMass_right_solution
    {omega one event complement sum inverseEvent target : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> Cont one inverseEvent target ->
        Cont event target one -> hsame complement target ∧ UnaryHistory target := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  intro _inverseRel targetRel
  have sumOne : hsame sum one :=
    hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne
  have eventComplementOne : Cont event complement one :=
    cont_result_hsame_transport sumRel sumOne
  have sameComplementTarget : hsame complement target :=
    cont_left_cancel eventComplementOne targetRel
  exact And.intro sameComplementTarget
    (unary_transport complementCarrier sameComplementTarget)

theorem ProbSpaceComplementMass_one_minus_singleton {omega one event complement sum rhs : BHist} :
    GroupSingletonCarrier event -> GroupSingletonCarrier one -> UnaryHistory complement ->
      Cont event complement sum -> hsame omega sum -> hsame omega one ->
      Cont one (GroupSingletonInv event) rhs -> hsame complement rhs ∧ UnaryHistory rhs := by
  intro eventCarrier oneCarrier complementCarrier eventComplement sameOmegaSum sameOmegaOne oneMinus
  have sumOne : hsame sum one := hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne
  have sumEmpty : hsame sum BHist.Empty := hsame_trans sumOne oneCarrier
  have eventComplementEmpty : append event complement = BHist.Empty :=
    Eq.trans eventComplement.symm sumEmpty
  have complementEmpty : hsame complement BHist.Empty :=
    (append_eq_empty_iff.mp eventComplementEmpty).right
  have rhsEmpty : hsame rhs BHist.Empty := hsame_trans oneMinus oneCarrier
  have sameComplementRhs : hsame complement rhs :=
    hsame_trans complementEmpty (hsame_symm rhsEmpty)
  exact And.intro sameComplementRhs (unary_transport complementCarrier sameComplementRhs)

theorem ProbSpaceMonotoneEvent_bounds {event gap middle rest omega one : BHist} :
    UnaryHistory event -> UnaryHistory gap -> UnaryHistory rest -> Cont event gap middle ->
      Cont middle rest omega -> hsame omega one ->
        PreorderPrefixLE event middle ∧ PreorderPrefixLE middle one ∧
          PreorderPrefixLE event one ∧ UnaryHistory middle ∧ UnaryHistory omega := by
  intro eventUnary gapUnary restUnary eventMiddle middleOmega sameOmegaOne
  have middleUnary : UnaryHistory middle :=
    unary_cont_closed eventUnary gapUnary eventMiddle
  have omegaUnary : UnaryHistory omega :=
    unary_cont_closed middleUnary restUnary middleOmega
  have eventMiddleLE : PreorderPrefixLE event middle :=
    Exists.intro gap (And.intro gapUnary eventMiddle)
  have middleOmegaLE : PreorderPrefixLE middle omega :=
    Exists.intro rest (And.intro restUnary middleOmega)
  have omegaOneLE : PreorderPrefixLE omega one :=
    PreorderPrefixLE_of_hsame sameOmegaOne
  have middleOneLE : PreorderPrefixLE middle one :=
    PreorderPrefixLE_trans middleOmegaLE omegaOneLE
  have eventOneLE : PreorderPrefixLE event one :=
    PreorderPrefixLE_trans eventMiddleLE middleOneLE
  exact And.intro eventMiddleLE
    (And.intro middleOneLE
      (And.intro eventOneLE (And.intro middleUnary omegaUnary)))

theorem ProbSpacePublicEventPacket_public_certificate_export
    {omega one event complement sum omega' one' event' complement' sum' : BHist} :
    ProbSpacePublicEventPacket omega one event complement sum ->
    hsame omega omega' ->
    hsame one one' ->
    hsame event event' ->
    hsame complement complement' ->
    hsame sum sum' ->
      hsame sum one ∧ PreorderPrefixLE event one ∧
        ProbSpacePublicEventPacket omega' one' event' complement' sum' ∧ hsame sum' one' ∧
          PreorderPrefixLE event' one' := by
  intro packet sameOmega sameOne sameEvent sameComplement sameSum
  have bounds :
      hsame sum one ∧ UnaryHistory sum ∧ Cont event complement sum ∧
        PreorderPrefixLE event one :=
    ProbSpacePublicEventPacket_normalization_bounds packet
  have transported :
      ProbSpacePublicEventPacket omega' one' event' complement' sum' ∧
        UnaryHistory event' ∧ UnaryHistory complement' ∧ Cont event' complement' sum' ∧
          hsame omega' one' ∧ hsame omega' sum' :=
    ProbSpacePublicEventPacket_transport_rows sameOmega sameOne sameEvent sameComplement sameSum
      packet
  have transportedBounds :
      hsame sum' one' ∧ UnaryHistory sum' ∧ Cont event' complement' sum' ∧
        PreorderPrefixLE event' one' :=
    ProbSpacePublicEventPacket_normalization_bounds transported.left
  exact
    ⟨bounds.left,
      bounds.right.right.right,
      transported.left,
      transportedBounds.left,
      transportedBounds.right.right.right⟩

def ProbSpaceBinaryCoverDifferenceLedger
    (event outside union intersection target : BHist) : Prop :=
  Cont event outside union ∧ Cont intersection outside target

theorem ProbSpaceBinaryCoverDifferenceLedger_inclusion_exclusion_identity
    {event outside union intersection target measuredUnion measuredIntersection lhs measuredEvent
      measuredTarget rhs : BHist} :
    ProbSpaceBinaryCoverDifferenceLedger event outside union intersection target ->
      hsame measuredUnion union ->
        hsame measuredIntersection intersection ->
          hsame measuredEvent event ->
            hsame measuredTarget target ->
              Cont measuredUnion measuredIntersection lhs ->
                Cont measuredEvent measuredTarget rhs ->
                  hsame (append outside intersection) (append intersection outside) ->
                    hsame lhs rhs := by
  intro ledger sameUnion sameIntersection sameEvent sameTarget lhsCont rhsCont outsideSwap
  cases sameUnion
  cases sameIntersection
  cases sameEvent
  cases sameTarget
  have lhsReadback : hsame lhs (append event (append outside intersection)) :=
    lhsCont.trans
      ((congrArg (fun row => append row intersection) ledger.left).trans
        (append_assoc event outside intersection))
  have rhsReadback : hsame rhs (append event (append intersection outside)) :=
    rhsCont.trans (congrArg (append event) ledger.right)
  have sameCanonical :
      hsame (append event (append outside intersection))
        (append event (append intersection outside)) :=
    congrArg (append event) outsideSwap
  exact hsame_trans lhsReadback (hsame_trans sameCanonical (hsame_symm rhsReadback))

theorem ProbSpaceBinaryCoverDifferenceLedger_inclusion_exclusion_balance
    {A I D U B muA muI muD muU muB leftTotal rightTotal : BHist} :
    UnaryHistory I -> UnaryHistory D -> Cont A D U -> Cont I D B -> hsame muA A ->
      hsame muI I -> hsame muD D -> hsame muU U -> hsame muB B ->
        Cont muU muI leftTotal -> Cont muA muB rightTotal ->
          hsame leftTotal rightTotal := by
  intro iUnary dUnary coverAD coverID sameMuA sameMuI sameMuD sameMuU sameMuB leftRow
    rightRow
  have uAD : hsame U (append A D) := coverAD
  have bID : hsame B (append I D) := coverID
  have muUAD : hsame muU (append A D) := hsame_trans sameMuU uAD
  have muBID : hsame muB (append I D) := hsame_trans sameMuB bID
  have muIUnary : UnaryHistory muI := unary_transport iUnary (hsame_symm sameMuI)
  have muDUnary : UnaryHistory muD := unary_transport dUnary (hsame_symm sameMuD)
  have muBAD : hsame muB (append muI muD) :=
    hsame_trans muBID
      (hsame_trans
        (congrArg (fun h => append h D) (hsame_symm sameMuI))
        (congrArg (fun h => append muI h) (hsame_symm sameMuD)))
  have rightAsAID : hsame rightTotal (append muA (append muI muD)) := by
    exact hsame_trans rightRow (congrArg (fun h => append muA h) muBAD)
  have leftAsADI : hsame leftTotal (append (append muA muD) muI) := by
    exact hsame_trans leftRow
      (hsame_trans
        (congrArg (fun h => append h muI) (hsame_trans muUAD
          (hsame_trans
            (congrArg (fun h => append h D) (hsame_symm sameMuA))
            (congrArg (fun h => append muA h) (hsame_symm sameMuD)))))
        (hsame_refl (append (append muA muD) muI)))
  have adIToAID : hsame (append (append muA muD) muI) (append muA (append muI muD)) :=
    hsame_trans (append_assoc muA muD muI)
      (congrArg (fun h => append muA h) (unary_append_comm_hsame muDUnary muIUnary))
  exact hsame_trans leftAsADI (hsame_trans adIToAID (hsame_symm rightAsAID))

def ProbSpaceTernaryInclusionExclusionLedger
    (a b c u v iab iac ibc k t : BHist) : Prop :=
  Cont b c v ∧ Cont a v u ∧ Cont iab iac k ∧ Cont k ibc t

theorem ProbSpaceTernaryInclusionExclusionLedger_identity
    {a b c u v iab iac ibc k t lhs rhs : BHist} :
    ProbSpaceTernaryInclusionExclusionLedger a b c u v iab iac ibc k t ->
      Cont (append (append (append u iab) iac) ibc) BHist.Empty lhs ->
        Cont (append (append (append a b) c) t) BHist.Empty rhs ->
          hsame lhs rhs := by
  intro ledger lhsCont rhsCont
  cases ledger with
  | intro bcV ledgerRest =>
      cases ledgerRest with
      | intro avU ledgerRest =>
          cases ledgerRest with
          | intro iabIacK kIbcT =>
              cases lhsCont
              cases rhsCont
              cases bcV
              cases avU
              cases iabIacK
              cases kIbcT
              have inner :
                  append (append (append (append a (append b c)) iab) iac) ibc =
                    append (append (append a b) c) (append (append iab iac) ibc) := by
                exact Eq.trans
                  (congrArg (fun row => append (append (append row iab) iac) ibc)
                    (append_assoc a b c).symm)
                  (Eq.trans
                      (append_assoc (append (append (append a b) c) iab) iac ibc)
                    (Eq.trans
                      (append_assoc (append (append a b) c) iab (append iac ibc))
                      (congrArg (fun row => append (append (append a b) c) row)
                        (append_assoc iab iac ibc).symm)))
              exact congrArg (fun row => append row BHist.Empty) inner

end BEDC.Derived.ProbSpaceUp

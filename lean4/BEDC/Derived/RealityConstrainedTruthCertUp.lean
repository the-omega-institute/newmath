import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RealityConstrainedTruthCertCarrier
    (source signature classifier tower stability descent invariant ledger failure name :
      BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory source ∧
    UnaryHistory signature ∧
      UnaryHistory tower ∧
        UnaryHistory stability ∧
          UnaryHistory invariant ∧
            UnaryHistory ledger ∧
              Cont source signature classifier ∧
                Cont tower stability descent ∧
                  Cont invariant ledger failure ∧
                    Cont ledger failure name

def RealityConstrainedTruthCertClassifier
    (source signature classifier tower stability descent invariant ledger failure name
      source' signature' classifier' tower' stability' descent' invariant' ledger' failure'
      name' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  hsame source source' ∧
    hsame signature signature' ∧
      hsame classifier classifier' ∧
        hsame tower tower' ∧
          hsame stability stability' ∧
            hsame descent descent' ∧
              hsame invariant invariant' ∧
                hsame ledger ledger' ∧ hsame failure failure' ∧ hsame name name'

theorem RealityConstrainedTruthCertClassifier_stability
    {source signature classifier tower stability descent invariant ledger failure name source'
      signature' classifier' tower' stability' descent' invariant' ledger' failure' name' :
      BHist} :
    RealityConstrainedTruthCertCarrier source signature classifier tower stability descent
        invariant ledger failure name →
      RealityConstrainedTruthCertClassifier source signature classifier tower stability descent
          invariant ledger failure name source' signature' classifier' tower' stability'
          descent' invariant' ledger' failure' name' →
        RealityConstrainedTruthCertCarrier source' signature' classifier' tower' stability'
            descent' invariant' ledger' failure' name' ∧
          Cont source' signature' classifier' ∧
            Cont tower' stability' descent' ∧
              Cont invariant' ledger' failure' ∧ Cont ledger' failure' name' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier classifierSame
  obtain ⟨unarySource, unarySignature, unaryTower, unaryStability, unaryInvariant,
    unaryLedger, sourceRoute, towerRoute, invariantRoute, ledgerRoute⟩ := carrier
  obtain ⟨sameSource, sameSignature, sameClassifier, sameTower, sameStability,
    sameDescent, sameInvariant, sameLedger, sameFailure, sameName⟩ := classifierSame
  have unarySource' : UnaryHistory source' :=
    unary_transport unarySource sameSource
  have unarySignature' : UnaryHistory signature' :=
    unary_transport unarySignature sameSignature
  have unaryTower' : UnaryHistory tower' :=
    unary_transport unaryTower sameTower
  have unaryStability' : UnaryHistory stability' :=
    unary_transport unaryStability sameStability
  have unaryInvariant' : UnaryHistory invariant' :=
    unary_transport unaryInvariant sameInvariant
  have unaryLedger' : UnaryHistory ledger' :=
    unary_transport unaryLedger sameLedger
  have sourceRoute' : Cont source' signature' classifier' :=
    cont_hsame_transport sameSource sameSignature sameClassifier sourceRoute
  have towerRoute' : Cont tower' stability' descent' :=
    cont_hsame_transport sameTower sameStability sameDescent towerRoute
  have invariantRoute' : Cont invariant' ledger' failure' :=
    cont_hsame_transport sameInvariant sameLedger sameFailure invariantRoute
  have ledgerRoute' : Cont ledger' failure' name' :=
    cont_hsame_transport sameLedger sameFailure sameName ledgerRoute
  exact
    ⟨⟨unarySource', unarySignature', unaryTower', unaryStability', unaryInvariant',
      unaryLedger', sourceRoute', towerRoute', invariantRoute', ledgerRoute'⟩,
      sourceRoute', towerRoute', invariantRoute', ledgerRoute'⟩

end BEDC.Derived.RealityConstrainedTruthCertUp

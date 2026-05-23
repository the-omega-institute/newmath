import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
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

theorem RealityConstrainedTruthCertNonescape
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N ledgerFailure failureRead exportRead : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x =
          [S, Sigma, K, T, U, D, I, L, F, N] /\
          Cont L F ledgerFailure /\ Cont F N failureRead /\
            Cont ledgerFailure N exportRead := by
  -- BEDC touchpoint anchor: BHist Cont
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact
        ⟨S, Sigma, K, T, U, D, I, L, F, N, append L F, append F N,
          append (append L F) N, rfl, rfl, rfl, rfl, rfl⟩

theorem RealityConstrainedTruthCertRootDefeatProjection [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N changedF failureRead openFitRoute classifierRead ledgerRead
      exportRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      Cont F N failureRead ->
        Cont changedF failureRead openFitRoute ->
          Cont openFitRoute K classifierRead ->
            Cont classifierRead L ledgerRead ->
              Cont ledgerRead N exportRead ->
                UnaryHistory changedF ->
                  PkgSig bundle exportRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row changedF ∨ hsame row N ∨
                            hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                        hsame ∧
                      UnaryHistory openFitRoute ∧
                        UnaryHistory classifierRead ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier failureRoute openFitRouteRoute classifierRoute ledgerRoute exportRoute
    changedFUnary exportPkg
  obtain ⟨sourceUnary, signatureUnary, towerUnary, stabilityUnary, invariantUnary,
    ledgerUnary, sourceRoute, _towerRoute, invariantRoute, nameRoute⟩ := carrier
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed failureUnary nameUnary failureRoute
  have openFitRouteUnary : UnaryHistory openFitRoute :=
    unary_cont_closed changedFUnary failureReadUnary openFitRouteRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed openFitRouteUnary classifierUnary classifierRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed classifierReadUnary ledgerUnary ledgerRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed ledgerReadUnary nameUnary exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row F ∨ hsame row changedF ∨ hsame row N ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact ⟨cert, openFitRouteUnary, classifierReadUnary, ledgerReadUnary, exportReadUnary⟩

theorem RealityConstrainedTruthCertRootLedgerNonescape [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N ledgerFailure failureName exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      Cont L F ledgerFailure ->
        Cont F N failureName ->
          Cont ledgerFailure failureName exportRead ->
            PkgSig bundle exportRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∨ hsame row F ∨ hsame row N ∨ hsame row exportRead)
                  (fun row : BHist =>
                    hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory ledgerFailure ∧
                  UnaryHistory failureName ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier ledgerFailureRoute failureNameRoute exportRoute exportPkg
  obtain ⟨_sourceUnary, _signatureUnary, _towerUnary, _stabilityUnary, invariantUnary,
    ledgerUnary, _sourceRoute, _towerRoute, invariantRoute, nameRoute⟩ := carrier
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have ledgerFailureUnary : UnaryHistory ledgerFailure :=
    unary_cont_closed ledgerUnary failureUnary ledgerFailureRoute
  have failureNameUnary : UnaryHistory failureName :=
    unary_cont_closed failureUnary nameUnary failureNameRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed ledgerFailureUnary failureNameUnary exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row L ∨ hsame row F ∨ hsame row N ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact ⟨cert, ledgerFailureUnary, failureNameUnary, exportReadUnary⟩

theorem RealityConstrainedTruthCertSiblingHandoffTotality [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N openFit objectivity explanation induction tower
      exportRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N →
      Cont S K openFit →
        Cont I L objectivity →
          Cont Sigma K explanation →
            Cont T U induction →
              Cont D L tower →
                Cont N tower exportRead →
                  PkgSig bundle exportRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row openFit ∨ hsame row objectivity ∨
                            hsame row explanation ∨ hsame row induction ∨
                              hsame row tower ∨ hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                        hsame ∧
                      UnaryHistory openFit ∧
                        UnaryHistory objectivity ∧
                          UnaryHistory explanation ∧
                            UnaryHistory induction ∧
                              UnaryHistory tower ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier openFitRoute objectivityRoute explanationRoute inductionRoute towerRoute
    exportRoute exportPkg
  obtain ⟨sourceUnary, signatureUnary, towerSourceUnary, stabilityUnary, invariantUnary,
    ledgerUnary, sourceRoute, towerSourceRoute, invariantRoute, nameRoute⟩ := carrier
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceRoute
  have descentUnary : UnaryHistory D :=
    unary_cont_closed towerSourceUnary stabilityUnary towerSourceRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have openFitUnary : UnaryHistory openFit :=
    unary_cont_closed sourceUnary classifierUnary openFitRoute
  have objectivityUnary : UnaryHistory objectivity :=
    unary_cont_closed invariantUnary ledgerUnary objectivityRoute
  have explanationUnary : UnaryHistory explanation :=
    unary_cont_closed signatureUnary classifierUnary explanationRoute
  have inductionUnary : UnaryHistory induction :=
    unary_cont_closed towerSourceUnary stabilityUnary inductionRoute
  have towerUnary : UnaryHistory tower :=
    unary_cont_closed descentUnary ledgerUnary towerRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed nameUnary towerUnary exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row openFit ∨ hsame row objectivity ∨ hsame row explanation ∨
            hsame row induction ∨ hsame row tower ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact ⟨source.left, exportPkg⟩
    }
  exact
    ⟨cert, openFitUnary, objectivityUnary, explanationUnary, inductionUnary, towerUnary,
      exportReadUnary⟩

theorem RealityConstrainedTruthCertRootConsumerTotality [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N failureRead openFitRead objectivityRead inductionRead
      towerRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      Cont F N failureRead ->
        Cont S K openFitRead ->
          Cont I L objectivityRead ->
            Cont U D inductionRead ->
              Cont T L towerRead ->
                Cont failureRead N exportRead ->
                  PkgSig bundle exportRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row openFitRead ∨ hsame row objectivityRead ∨
                            hsame row inductionRead ∨ hsame row towerRead ∨
                              hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                        hsame ∧
                      UnaryHistory openFitRead ∧
                        UnaryHistory objectivityRead ∧
                          UnaryHistory inductionRead ∧
                            UnaryHistory towerRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro carrier failureRoute openFitRoute objectivityRoute inductionRoute towerReadRoute
    exportRoute exportPkg
  obtain ⟨sourceUnary, _signatureUnary, towerUnary, stabilityUnary, invariantUnary,
    ledgerUnary, sourceRoute, towerRoute, invariantRoute, nameRoute⟩ := carrier
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary _signatureUnary sourceRoute
  have descentUnary : UnaryHistory D :=
    unary_cont_closed towerUnary stabilityUnary towerRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed failureUnary nameUnary failureRoute
  have openFitReadUnary : UnaryHistory openFitRead :=
    unary_cont_closed sourceUnary classifierUnary openFitRoute
  have objectivityReadUnary : UnaryHistory objectivityRead :=
    unary_cont_closed invariantUnary ledgerUnary objectivityRoute
  have inductionReadUnary : UnaryHistory inductionRead :=
    unary_cont_closed stabilityUnary descentUnary inductionRoute
  have towerReadUnary : UnaryHistory towerRead :=
    unary_cont_closed towerUnary ledgerUnary towerReadRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed failureReadUnary nameUnary exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row openFitRead ∨ hsame row objectivityRead ∨
            hsame row inductionRead ∨ hsame row towerRead ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact
    ⟨cert, openFitReadUnary, objectivityReadUnary, inductionReadUnary, towerReadUnary,
      exportReadUnary⟩

theorem RealityConstrainedTruthCertObserverInvariantLedgerRoute [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N invariantLedger exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      Cont I L invariantLedger ->
        Cont invariantLedger N exportRead ->
          PkgSig bundle exportRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row L ∨ hsame row N ∨ hsame row exportRead)
                (fun row : BHist =>
                  hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                hsame ∧
              UnaryHistory invariantLedger ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier invariantLedgerRoute exportRoute exportPkg
  obtain ⟨_sourceUnary, _signatureUnary, _towerUnary, _stabilityUnary, invariantUnary,
    ledgerUnary, _sourceRoute, _towerRoute, invariantRoute, nameRoute⟩ := carrier
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have invariantLedgerUnary : UnaryHistory invariantLedger :=
    unary_cont_closed invariantUnary ledgerUnary invariantLedgerRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed invariantLedgerUnary nameUnary exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row I ∨ hsame row L ∨ hsame row N ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact ⟨cert, invariantLedgerUnary, exportReadUnary⟩

theorem RealityConstrainedTruthCertRootClassifierStability [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N S' Sigma' K' T' U' D' I' L' F' N' classifierRead
      exportRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N →
    RealityConstrainedTruthCertClassifier S Sigma K T U D I L F N S' Sigma' K'
      T' U' D' I' L' F' N' →
    Cont K K' classifierRead →
    Cont classifierRead N' exportRead →
    PkgSig bundle exportRead pkg →
    SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row K' ∨ hsame row classifierRead ∨
            hsame row exportRead)
        (fun row : BHist =>
          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame ∧
      UnaryHistory classifierRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier classifierSame classifierRoute exportRoute exportPkg
  have transported :=
    RealityConstrainedTruthCertClassifier_stability carrier classifierSame
  obtain ⟨sourceUnary, signatureUnary, _towerUnary, _stabilityUnary, _invariantUnary,
    _ledgerUnary, sourceRoute, _towerRoute, _invariantRoute, _nameRoute⟩ := carrier
  obtain ⟨transportedCarrier, _sourceRoute', _towerRoute', invariantRoute', nameRoute'⟩ :=
    transported
  obtain ⟨_sourceUnary', _signatureUnary', _towerUnary', _stabilityUnary',
    invariantUnary', ledgerUnary', _sourceRoute'', _towerRoute'', _invariantRoute',
    _nameRoute'⟩ := transportedCarrier
  obtain ⟨_sameSource, _sameSignature, sameClassifier, _sameTower, _sameStability,
    _sameDescent, _sameInvariant, _sameLedger, _sameFailure, _sameName⟩ :=
    classifierSame
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceRoute
  have failureUnary' : UnaryHistory F' :=
    unary_cont_closed invariantUnary' ledgerUnary' invariantRoute'
  have nameUnary' : UnaryHistory N' :=
    unary_cont_closed ledgerUnary' failureUnary' nameRoute'
  have classifierUnary' : UnaryHistory K' :=
    unary_transport classifierUnary sameClassifier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed classifierUnary classifierUnary' classifierRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed classifierReadUnary nameUnary' exportRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row K' ∨ hsame row classifierRead ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact ⟨cert, classifierReadUnary, exportReadUnary⟩

end BEDC.Derived.RealityConstrainedTruthCertUp

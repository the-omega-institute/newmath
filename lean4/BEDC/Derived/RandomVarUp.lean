import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RandomVarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def RandomVarTotalDefectEvent (sourceTotal chosenPreimage defect : BHist) : Prop :=
  Cont chosenPreimage defect sourceTotal

theorem RandomVarTotalPreimage_composition_exactness
    {sourceTotal middleTotal targetTotal middlePreimage compositePreimage : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory middleTotal -> hsame targetTotal BHist.Empty ->
      hsame middleTotal BHist.Empty -> Cont middleTotal targetTotal middlePreimage ->
        Cont sourceTotal middlePreimage compositePreimage ->
          UnaryHistory compositePreimage ∧ hsame compositePreimage sourceTotal := by
  intro sourceUnary _middleUnary targetEmpty middleEmpty middleReadback compositeReadback
  have middleTargetEmpty : Cont middleTotal BHist.Empty middlePreimage :=
    cont_hsame_transport (hsame_refl middleTotal) targetEmpty (hsame_refl middlePreimage)
      middleReadback
  have middlePreimageSame : hsame middlePreimage middleTotal :=
    cont_right_unit_result middleTargetEmpty
  have middlePreimageEmpty : hsame middlePreimage BHist.Empty :=
    hsame_trans middlePreimageSame middleEmpty
  have compositeRightUnit : Cont sourceTotal BHist.Empty compositePreimage :=
    cont_hsame_transport (hsame_refl sourceTotal) middlePreimageEmpty
      (hsame_refl compositePreimage) compositeReadback
  have compositeSame : hsame compositePreimage sourceTotal :=
    cont_right_unit_result compositeRightUnit
  exact And.intro (unary_transport sourceUnary (hsame_symm compositeSame)) compositeSame

structure RandomVarTotalReadbackCertificate
    (targetTotal sourceTotal chosenPreimage : BHist) : Prop where
  chosen_readback : Cont targetTotal BHist.Empty chosenPreimage
  carried_total_bridge : Cont targetTotal BHist.Empty sourceTotal

theorem RandomVarTotalReadbackCertificate_total_event_preimage_exactness
    {targetTotal sourceTotal chosenPreimage : BHist} :
    UnaryHistory sourceTotal ->
      RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
        UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal := by
  intro sourceUnary cert
  have chosenSource : hsame chosenPreimage sourceTotal :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact And.intro (unary_transport sourceUnary (hsame_symm chosenSource)) chosenSource

theorem RandomVarTotalReadbackCertificate_source_coverage
    {targetTotal sourceTotal chosenPreimage sourcePoint gap : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont sourcePoint gap sourceTotal -> Cont sourcePoint gap chosenPreimage := by
  intro cert sourceCoverage
  have chosenSource : hsame chosenPreimage sourceTotal :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact cont_result_hsame_transport sourceCoverage (hsame_symm chosenSource)

theorem RandomVarTotalReadbackCertificate_composition_total_event_preimage_exactness
    {omegaU omegaT omegaS preY preX preYX : BHist} :
    RandomVarTotalReadbackCertificate omegaU omegaT preY ->
      RandomVarTotalReadbackCertificate omegaT omegaS preX ->
        Cont preY BHist.Empty preYX ->
          hsame preYX omegaS ∧ hsame preYX preY ∧ hsame preY omegaT ∧ hsame preX omegaS := by
  intro upperCert lowerCert compositeReadback
  have compositeChosen : hsame preYX preY :=
    cont_deterministic compositeReadback (cont_right_unit preY)
  have upperChosenTarget : hsame preY omegaT :=
    cont_deterministic upperCert.chosen_readback upperCert.carried_total_bridge
  have lowerTargetSource : hsame omegaT omegaS :=
    cont_deterministic (cont_right_unit omegaT) lowerCert.carried_total_bridge
  have lowerChosenSource : hsame preX omegaS :=
    cont_deterministic lowerCert.chosen_readback lowerCert.carried_total_bridge
  exact And.intro (hsame_trans compositeChosen (hsame_trans upperChosenTarget lowerTargetSource))
    (And.intro compositeChosen (And.intro upperChosenTarget lowerChosenSource))

theorem RandomVarTotalReadbackCertificate_carried_bridge_chosen_preimage_exactness_iff
    {targetTotal sourceTotal chosenPreimage : BHist} :
    Cont targetTotal BHist.Empty chosenPreimage ->
      (Cont targetTotal BHist.Empty sourceTotal ↔ hsame chosenPreimage sourceTotal) := by
  intro chosenReadback
  constructor
  · intro carriedBridge
    exact cont_deterministic chosenReadback carriedBridge
  · intro chosenExact
    exact cont_result_hsame_transport chosenReadback chosenExact

theorem RandomVarTotalDefectEvent_vanishing_total_exactness_iff
    {sourceTotal chosenPreimage defect : BHist} :
    RandomVarTotalDefectEvent sourceTotal chosenPreimage defect ->
      (hsame chosenPreimage sourceTotal ↔ hsame defect BHist.Empty) := by
  intro defectEvent
  constructor
  · intro chosenExact
    have transportedEvent : Cont sourceTotal defect sourceTotal :=
      cont_hsame_transport chosenExact (hsame_refl defect) (hsame_refl sourceTotal) defectEvent
    exact cont_right_unit_unique transportedEvent
  · intro defectEmpty
    have rightUnitEvent : Cont chosenPreimage BHist.Empty sourceTotal :=
      cont_hsame_transport (hsame_refl chosenPreimage) defectEmpty (hsame_refl sourceTotal)
        defectEvent
    exact hsame_symm (cont_right_unit_result rightUnitEvent)

theorem RandomVarTerminalPreimage_coverage_defect_iff
    {sourceTotal chosenPreimage defect : BHist} :
    UnaryHistory sourceTotal -> RandomVarTotalDefectEvent sourceTotal chosenPreimage defect ->
      ((forall {h gap : BHist}, UnaryHistory h -> Cont h gap sourceTotal ->
          Cont h gap chosenPreimage) ↔ hsame defect BHist.Empty) := by
  intro _sourceUnary defectEvent
  constructor
  · intro coverage
    have chosenExact : hsame chosenPreimage sourceTotal :=
      cont_deterministic
        (coverage (h := sourceTotal) (gap := BHist.Empty) _sourceUnary
          (cont_right_unit sourceTotal))
        (cont_right_unit sourceTotal)
    exact (RandomVarTotalDefectEvent_vanishing_total_exactness_iff defectEvent).mp
      chosenExact
  · intro defectEmpty
    have chosenExact : hsame chosenPreimage sourceTotal :=
      (RandomVarTotalDefectEvent_vanishing_total_exactness_iff defectEvent).mpr defectEmpty
    intro h gap _sourceUnary sourceCoverage
    exact cont_result_hsame_transport sourceCoverage (hsame_symm chosenExact)

theorem RandomVarTerminalPreimage_no_loss_boundary
    {sourceTotal chosenPreimage defect : BHist} {Covers : BHist -> BHist -> Prop} :
    RandomVarTotalDefectEvent sourceTotal chosenPreimage defect ->
      (forall {h event event' : BHist}, hsame event event' -> Covers h event ->
        Covers h event') ->
        (forall h : BHist, Covers h sourceTotal) ->
          ((forall h : BHist, Covers h chosenPreimage) ->
            hsame chosenPreimage sourceTotal) ->
            (hsame chosenPreimage sourceTotal ↔ hsame defect BHist.Empty) ∧
              (hsame chosenPreimage sourceTotal -> forall h : BHist,
                Covers h chosenPreimage) ∧
                ((forall h : BHist, Covers h chosenPreimage) ->
                  hsame chosenPreimage sourceTotal) := by
  intro defectEvent coverTransport sourceCoverage coverageComplete
  have defectExact :
      hsame chosenPreimage sourceTotal ↔ hsame defect BHist.Empty :=
    RandomVarTotalDefectEvent_vanishing_total_exactness_iff defectEvent
  constructor
  · exact defectExact
  · constructor
    · intro sameChosen h
      exact coverTransport (h := h) (hsame_symm sameChosen) (sourceCoverage h)
    · exact coverageComplete

theorem RandomVarTotalReadbackCertificate_total_target_reflection_criterion
    {targetTotal sourceTotal chosenPreimage targetEvent eventPreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont targetEvent BHist.Empty eventPreimage ->
        hsame targetEvent targetTotal -> hsame eventPreimage sourceTotal := by
  intro readbackCert eventReadback eventTarget
  have targetReadback : Cont targetTotal BHist.Empty eventPreimage :=
    cont_hsame_transport eventTarget (hsame_refl BHist.Empty) (hsame_refl eventPreimage)
      eventReadback
  exact cont_deterministic targetReadback readbackCert.carried_total_bridge

theorem RandomVarPreimage_disjoint_binary_union_exactness
    {B C U_T A_B A_C A_U U_S : BHist} :
    hsame A_B B -> hsame A_C C -> hsame A_U U_T -> Cont B C U_T ->
      Cont A_B A_C U_S -> (hsame B C -> False) ->
        hsame A_U U_S ∧ (hsame A_B A_C -> False) := by
  intro samePreimageB samePreimageC samePreimageUnion targetUnion sourceUnion targetDisjoint
  have transportedUnion : hsame U_T U_S :=
    cont_respects_hsame (hsame_symm samePreimageB) (hsame_symm samePreimageC)
      targetUnion sourceUnion
  have sourceDisjoint : hsame A_B A_C -> False := by
    intro sameSource
    exact targetDisjoint
      (hsame_trans (hsame_symm samePreimageB) (hsame_trans sameSource samePreimageC))
  exact And.intro (hsame_trans samePreimageUnion transportedUnion) sourceDisjoint

theorem RandomVarPreimage_relative_difference_exactness
    {A B D_T A_S B_S D_X D_S : BHist} :
    hsame A_S A -> hsame B_S B -> hsame D_X D_T -> Cont B D_T A ->
      Cont B_S D_S A_S -> hsame D_X D_S := by
  intro sameSourceEndpoint sameSourceBase sameDiffTarget targetDifference sourceDifference
  have sourceAtTarget : Cont B D_S A :=
    cont_hsame_transport sameSourceBase (hsame_refl D_S) sameSourceEndpoint sourceDifference
  have targetDiffSourceDiff : hsame D_T D_S :=
    cont_left_cancel targetDifference sourceAtTarget
  exact hsame_trans sameDiffTarget targetDiffSourceDiff

theorem RandomVarPreimage_symmetric_difference_exactness
    {A B diffAB diffBA deltaT preA preB preDiffAB preDiffBA preDelta sourceDiffAB
      sourceDiffBA sourceDelta : BHist} :
    hsame preA A -> hsame preB B -> hsame preDiffAB diffAB -> hsame preDiffBA diffBA ->
      hsame preDelta deltaT -> Cont B diffAB A -> Cont A diffBA B ->
        Cont diffAB diffBA deltaT -> Cont preB sourceDiffAB preA ->
          Cont preA sourceDiffBA preB -> Cont sourceDiffAB sourceDiffBA sourceDelta ->
            (hsame diffAB diffBA -> False) ->
              hsame preDelta sourceDelta ∧ (hsame sourceDiffAB sourceDiffBA -> False) := by
  intro samePreA samePreB samePreDiffAB samePreDiffBA samePreDelta targetDiffAB
    targetDiffBA targetDelta sourceDiffABRow sourceDiffBARow sourceDeltaRow targetDisjoint
  have sourceDiffABExact : hsame preDiffAB sourceDiffAB :=
    RandomVarPreimage_relative_difference_exactness samePreA samePreB samePreDiffAB
      targetDiffAB sourceDiffABRow
  have sourceDiffBAExact : hsame preDiffBA sourceDiffBA :=
    RandomVarPreimage_relative_difference_exactness samePreB samePreA samePreDiffBA
      targetDiffBA sourceDiffBARow
  have sourceDiffABTarget : hsame sourceDiffAB diffAB :=
    hsame_trans (hsame_symm sourceDiffABExact) samePreDiffAB
  have sourceDiffBATarget : hsame sourceDiffBA diffBA :=
    hsame_trans (hsame_symm sourceDiffBAExact) samePreDiffBA
  exact RandomVarPreimage_disjoint_binary_union_exactness sourceDiffABTarget sourceDiffBATarget
    samePreDelta targetDelta sourceDeltaRow targetDisjoint

theorem RandomVarPreimage_complement_difference_exactness
    {omegaT omegaS preOmega B BTComp BS BComp preComp : BHist} :
    RandomVarTotalReadbackCertificate omegaT omegaS preOmega -> hsame BS B ->
      hsame preComp BTComp -> Cont B BTComp omegaT -> Cont BS BComp omegaS ->
        hsame preComp BComp ∧ hsame preOmega omegaS := by
  intro cert sameBase samePreComp targetComplement sourceComplement
  have sameTotals : hsame omegaT omegaS :=
    cont_deterministic (cont_right_unit omegaT) cert.carried_total_bridge
  have targetComplementAtSourceTotal : Cont B BTComp omegaS :=
    cont_result_hsame_transport targetComplement sameTotals
  have sourceComplementAtTargetBase : Cont B BComp omegaS :=
    cont_hsame_transport sameBase (hsame_refl BComp) (hsame_refl omegaS) sourceComplement
  have sameTargetSourceComp : hsame BTComp BComp :=
    cont_left_cancel targetComplementAtSourceTotal sourceComplementAtTargetBase
  have samePreOmegaSource : hsame preOmega omegaS :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact And.intro (hsame_trans samePreComp sameTargetSourceComp) samePreOmegaSource

theorem RandomVarTotalReadbackCertificate_terminal_readback_uniqueness
    {targetTotal sourceTotal chosenPreimage alternatePreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont targetTotal BHist.Empty alternatePreimage ->
        hsame alternatePreimage sourceTotal ∧ hsame alternatePreimage chosenPreimage := by
  intro cert alternateReadback
  have sameAlternateSource : hsame alternatePreimage sourceTotal :=
    cont_deterministic alternateReadback cert.carried_total_bridge
  have sameAlternateChosen : hsame alternatePreimage chosenPreimage :=
    cont_deterministic alternateReadback cert.chosen_readback
  exact And.intro sameAlternateSource sameAlternateChosen

theorem RandomVarTotalReadbackCertificate_partiality_obstruction
    {targetTotal sourceTotal chosenPreimage h : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      UnaryHistory h ->
        Cont h BHist.Empty sourceTotal ->
          (Cont h BHist.Empty chosenPreimage -> False) -> False := by
  intro cert _sourceUnary sourceCoverage chosenNoncoverage
  have chosenSource : hsame chosenPreimage sourceTotal :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  have chosenCoverage : Cont h BHist.Empty chosenPreimage :=
    cont_result_hsame_transport sourceCoverage (hsame_symm chosenSource)
  exact chosenNoncoverage chosenCoverage

theorem RandomVarTotalReadbackCertificate_minimal_obstruction
    {targetTotal sourceTotal chosenPreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      (UnaryHistory sourceTotal ->
          UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal) ∧
        ((hsame chosenPreimage sourceTotal -> False) ->
          RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage -> False) := by
  intro cert
  constructor
  · intro sourceUnary
    exact RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary cert
  · intro obstruction certAgain
    exact obstruction (cont_deterministic certAgain.chosen_readback certAgain.carried_total_bridge)

theorem RandomVarPreimage_empty_event_exactness
    {targetEmpty sourceEmpty preimage : BHist} :
    hsame targetEmpty BHist.Empty -> hsame sourceEmpty BHist.Empty ->
      Cont targetEmpty BHist.Empty preimage -> hsame preimage sourceEmpty := by
  intro targetEmptyZero sourceEmptyZero preimageReadback
  have preimageTarget : hsame preimage targetEmpty :=
    cont_right_unit_result preimageReadback
  exact hsame_trans preimageTarget (hsame_trans targetEmptyZero (hsame_symm sourceEmptyZero))

def RandomVarPreimageUnionFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (RandomVarPreimageUnionFold xs)

theorem RandomVarPreimage_countable_union_exactness
    (left right : ProbeBundle BHist) :
    hsame (RandomVarPreimageUnionFold (bundleAppend left right))
      (append (RandomVarPreimageUnionFold left) (RandomVarPreimageUnionFold right)) := by
  induction left with
  | Bnil =>
      exact (append_empty_left (RandomVarPreimageUnionFold right)).symm
  | Bcons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (RandomVarPreimageUnionFold xs)
          (RandomVarPreimageUnionFold right)).symm

theorem RandomVarTerminalPreimage_exactness_coverage_iff
    {sourceTotal chosenPreimage : BHist} :
    UnaryHistory sourceTotal ->
      ((forall {h gap : BHist}, UnaryHistory h -> Cont h gap sourceTotal ->
          Cont h gap chosenPreimage) <-> hsame chosenPreimage sourceTotal) := by
  intro sourceUnary
  constructor
  · intro coverage
    have sourceCoverage : Cont sourceTotal BHist.Empty chosenPreimage :=
      coverage sourceUnary (cont_right_unit sourceTotal)
    exact cont_right_unit_result sourceCoverage
  · intro chosenExact
    intro h gap _unaryH sourceCoverage
    exact cont_result_hsame_transport sourceCoverage (hsame_symm chosenExact)

theorem RandomVarPreimage_binary_intersection_exactness
    {targetLeft targetRight targetIntersection sourceLeft sourceRight sourceIntersection
      sourcePreimageIntersection : BHist} :
    hsame sourceLeft targetLeft -> hsame sourceRight targetRight ->
      hsame sourcePreimageIntersection targetIntersection ->
        hsame targetIntersection (append targetLeft targetRight) ->
          Cont sourceLeft sourceRight sourceIntersection ->
            hsame sourcePreimageIntersection sourceIntersection ∧
              hsame sourceIntersection (append sourceLeft sourceRight) := by
  intro sameLeft sameRight samePreimage targetIntersectionReadback sourceIntersectionCont
  have targetIntersectionCont : Cont targetLeft targetRight targetIntersection :=
    targetIntersectionReadback
  have sameTargetSourceIntersection : hsame targetIntersection sourceIntersection :=
    cont_respects_hsame (hsame_symm sameLeft) (hsame_symm sameRight) targetIntersectionCont
      sourceIntersectionCont
  exact And.intro (hsame_trans samePreimage sameTargetSourceIntersection) sourceIntersectionCont

theorem RandomVarCountablePreimageIntersection_exactness
    {source target intersection witness : BHist} :
    UnaryHistory source ->
      Cont target intersection witness ->
        RandomVarTotalReadbackCertificate target source witness ->
          UnaryHistory witness ∧ hsame witness source := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame RandomVarTotalReadbackCertificate
  intro sourceUnary targetIntersectionReadback cert
  have intersectionEmpty : hsame intersection BHist.Empty :=
    cont_left_cancel targetIntersectionReadback cert.chosen_readback
  have displayedTotalReadback : Cont target BHist.Empty witness :=
    cont_hsame_transport (hsame_refl target) intersectionEmpty (hsame_refl witness)
      targetIntersectionReadback
  have witnessSource : hsame witness source :=
    cont_deterministic displayedTotalReadback cert.carried_total_bridge
  exact ⟨unary_transport sourceUnary (hsame_symm witnessSource), witnessSource⟩

theorem RandomVarCountablePreimageIntersection_witness_determinacy
    {source target intersection witness witnessPrime : BHist} :
    UnaryHistory source ->
      Cont target intersection witness ->
        Cont target intersection witnessPrime ->
          RandomVarTotalReadbackCertificate target source witness ->
            RandomVarTotalReadbackCertificate target source witnessPrime ->
              hsame witness witnessPrime := by
  -- BEDC touchpoint anchor: BHist Cont hsame RandomVarTotalReadbackCertificate
  intro _sourceUnary targetIntersectionReadback targetIntersectionReadbackPrime cert certPrime
  have intersectionEmpty : hsame intersection BHist.Empty :=
    cont_left_cancel targetIntersectionReadback cert.chosen_readback
  have displayedReadback : Cont target BHist.Empty witness :=
    cont_hsame_transport (hsame_refl target) intersectionEmpty (hsame_refl witness)
      targetIntersectionReadback
  have witnessSource : hsame witness source :=
    cont_deterministic displayedReadback cert.carried_total_bridge
  have intersectionEmptyPrime : hsame intersection BHist.Empty :=
    cont_left_cancel targetIntersectionReadbackPrime certPrime.chosen_readback
  have displayedReadbackPrime : Cont target BHist.Empty witnessPrime :=
    cont_hsame_transport (hsame_refl target) intersectionEmptyPrime
      (hsame_refl witnessPrime) targetIntersectionReadbackPrime
  have witnessPrimeSource : hsame witnessPrime source :=
    cont_deterministic displayedReadbackPrime certPrime.carried_total_bridge
  exact hsame_trans witnessSource (hsame_symm witnessPrimeSource)

theorem RandomVarMartingaleFiltration_handoff [AskSetup] [PackageSetup]
    {sourceProb preimage totalReadback filtration transport replay provenance localName
      preimageRead totalEndpoint filtrationRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory sourceProb -> UnaryHistory preimage -> UnaryHistory totalReadback ->
      UnaryHistory filtration -> UnaryHistory localName ->
        Cont sourceProb preimage preimageRead ->
          Cont preimageRead totalReadback totalEndpoint ->
            Cont totalEndpoint filtration filtrationRead ->
              Cont filtrationRead localName namedRead ->
                PkgSig bundle provenance pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sourceProb ∨ hsame row preimage ∨
                          hsame row totalReadback ∨ hsame row filtration ∨
                            hsame row transport ∨ hsame row replay ∨
                              hsame row provenance ∨ hsame row localName ∨
                                hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont sourceProb preimage preimageRead ∧
                          Cont preimageRead totalReadback totalEndpoint ∧
                            Cont totalEndpoint filtration filtrationRead ∧
                              Cont filtrationRead localName namedRead ∧
                                PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unarySource unaryPreimage unaryTotal unaryFiltration unaryLocal preimageRoute
    totalRoute filtrationRoute namedRoute provenanceSig
  have preimageReadUnary : UnaryHistory preimageRead :=
    unary_cont_closed unarySource unaryPreimage preimageRoute
  have totalEndpointUnary : UnaryHistory totalEndpoint :=
    unary_cont_closed preimageReadUnary unaryTotal totalRoute
  have filtrationReadUnary : UnaryHistory filtrationRead :=
    unary_cont_closed totalEndpointUnary unaryFiltration filtrationRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed filtrationReadUnary unaryLocal namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceProb ∨ hsame row preimage ∨ hsame row totalReadback ∨
              hsame row filtration ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceProb preimage preimageRead ∧
              Cont preimageRead totalReadback totalEndpoint ∧
                Cont totalEndpoint filtration filtrationRead ∧
                  Cont filtrationRead localName namedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, preimageRoute, totalRoute, filtrationRoute, namedRoute,
          provenanceSig⟩
  }
  exact ⟨cert, namedUnary⟩

theorem RandomVarProbSpaceDistribution_sibling_route [AskSetup] [PackageSetup]
    {probSource measurableTarget preimage classifier transport replay provenance localName
      distributionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory probSource -> UnaryHistory measurableTarget -> UnaryHistory preimage ->
      UnaryHistory classifier -> UnaryHistory distributionRead -> UnaryHistory localName ->
        Cont probSource measurableTarget preimage ->
          Cont preimage classifier distributionRead ->
            Cont distributionRead localName namedRead ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row probSource ∨ hsame row measurableTarget ∨
                        hsame row preimage ∨ hsame row classifier ∨
                          hsame row transport ∨ hsame row replay ∨
                            hsame row provenance ∨ hsame row localName ∨
                              hsame row distributionRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont probSource measurableTarget preimage ∧
                        Cont preimage classifier distributionRead ∧
                          Cont distributionRead localName namedRead ∧
                            PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryProb unaryMeasurable _unaryPreimage unaryClassifier unaryDistribution
    unaryLocal probPreimageRoute distributionRoute namedRoute provenanceSig
  have preimageUnary : UnaryHistory preimage :=
    unary_cont_closed unaryProb unaryMeasurable probPreimageRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed preimageUnary unaryClassifier distributionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed distributionUnary unaryLocal namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row probSource ∨ hsame row measurableTarget ∨ hsame row preimage ∨
              hsame row classifier ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row distributionRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont probSource measurableTarget preimage ∧
              Cont preimage classifier distributionRead ∧
                Cont distributionRead localName namedRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro distributionRead ⟨hsame_refl distributionRead, distributionUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right; right; right; right; right; right; right; right; left
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, probPreimageRoute, distributionRoute, namedRoute,
          provenanceSig⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.RandomVarUp

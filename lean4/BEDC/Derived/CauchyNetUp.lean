import BEDC.Derived.CauchyNetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyNetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyNetCarrier [AskSetup] [PackageSetup]
    (directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory directed ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧
    UnaryHistory dyadic ∧ UnaryHistory classifier ∧ UnaryHistory realHandoff ∧
      UnaryHistory nameRow ∧ Cont directed schedule regseq ∧
        Cont classifier realHandoff route ∧ Cont route transport provenance ∧
          PkgSig bundle provenance pkg

theorem CauchyNetCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
        provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport
              route provenance nameRow bundle pkg ∧ hsame row realHandoff)
          (fun row : BHist => hsame row classifier ∨ hsame row realHandoff)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row realHandoff)
          hsame ∧
        UnaryHistory classifier ∧ UnaryHistory realHandoff ∧
          Cont directed schedule regseq ∧ Cont classifier realHandoff route ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierSurface := carrier
  obtain ⟨_directedUnary, _scheduleUnary, _regseqUnary, _dyadicUnary, classifierUnary,
    realHandoffUnary, _nameRowUnary, directedScheduleRegseq, classifierRealRoute,
    _routeTransportProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport
            route provenance nameRow bundle pkg ∧ hsame row realHandoff)
        (fun row : BHist => hsame row classifier ∨ hsame row realHandoff)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row realHandoff)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realHandoff ⟨carrierSurface, hsame_refl realHandoff⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.right
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.right⟩
    }
  exact
    ⟨cert, classifierUnary, realHandoffUnary, directedScheduleRegseq, classifierRealRoute,
      provenancePkg⟩

theorem CauchyNetCarrier_transport_semanticNameCert [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow transportedReal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
        provenance nameRow bundle pkg →
      UnaryHistory transportedReal →
        hsame transportedReal realHandoff →
          SemanticNameCert
            (fun row : BHist => hsame row transportedReal ∧ UnaryHistory row)
            (fun row : BHist => hsame row classifier ∨ hsame row transportedReal)
            (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row transportedReal)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier transportedUnary _transportedMatchesReal
  obtain ⟨_directedUnary, _scheduleUnary, _regseqUnary, _dyadicUnary,
    _classifierUnary, _realHandoffUnary, _nameRowUnary, _directedScheduleRegseq,
    _classifierRealRoute, _routeTransportProvenance, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro transportedReal ⟨hsame_refl transportedReal, transportedUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }

theorem CauchyNetCarrier_commonWindow_semanticNameCert [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
        provenance nameRow bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row classifier ∧ UnaryHistory row)
        (fun row : BHist => hsame row directed ∨ hsame row schedule ∨ hsame row classifier)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row classifier)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_directedUnary, _scheduleUnary, _regseqUnary, _dyadicUnary, classifierUnary,
    _realHandoffUnary, _nameRowUnary, _directedScheduleRegseq, _classifierRealRoute,
    _routeTransportProvenance, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro classifier ⟨hsame_refl classifier, classifierUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }

theorem CauchyNetDirectedWindow_localization [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance nameRow
      restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic restrictedClassifier
      restrictedReal restrictedTransport restrictedRoute restrictedProvenance restrictedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
        provenance nameRow bundle pkg →
      CauchyNetCarrier restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic
          restrictedClassifier restrictedReal restrictedTransport restrictedRoute
          restrictedProvenance restrictedName bundle pkg →
        Cont restrictedRegseq restrictedReal restrictedRoute →
          PkgSig bundle restrictedProvenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row restrictedReal ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row restrictedDirected ∨ hsame row restrictedSchedule ∨
                    hsame row restrictedRegseq ∨ hsame row restrictedClassifier ∨
                      hsame row restrictedReal)
                (fun row : BHist => PkgSig bundle restrictedProvenance pkg ∧
                  hsame row restrictedReal)
                hsame ∧
              UnaryHistory restrictedReal ∧
                Cont restrictedRegseq restrictedReal restrictedRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro _carrier restrictedCarrier restrictedCont restrictedPkg
  obtain ⟨_restrictedDirectedUnary, _restrictedScheduleUnary, restrictedRegseqUnary,
    _restrictedDyadicUnary, _restrictedClassifierUnary, restrictedRealUnary,
    _restrictedNameUnary, _restrictedDirectedScheduleRegseq,
    _restrictedClassifierRealRoute, _restrictedRouteTransportProvenance,
    _restrictedCarrierPkg⟩ := restrictedCarrier
  have _restrictedRouteUnary : UnaryHistory restrictedRoute :=
    unary_cont_closed restrictedRegseqUnary restrictedRealUnary restrictedCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row restrictedReal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row restrictedDirected ∨ hsame row restrictedSchedule ∨
            hsame row restrictedRegseq ∨ hsame row restrictedClassifier ∨
              hsame row restrictedReal)
        (fun row : BHist => PkgSig bundle restrictedProvenance pkg ∧
          hsame row restrictedReal)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro restrictedReal ⟨hsame_refl restrictedReal, restrictedRealUnary⟩
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
        exact ⟨restrictedPkg, source.left⟩
    }
  exact ⟨cert, restrictedRealUnary, restrictedCont⟩

def CauchyNetWitnessCompleteSubwindow [AskSetup] [PackageSetup]
    (directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic
      restrictedClassifier restrictedReal restrictedTransport restrictedRoute
      restrictedProvenance restrictedName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
      provenance nameRow bundle pkg ∧
    CauchyNetCarrier restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic
      restrictedClassifier restrictedReal restrictedTransport restrictedRoute restrictedProvenance
      restrictedName bundle pkg ∧
    Cont restrictedRegseq restrictedReal restrictedRoute ∧
      PkgSig bundle restrictedProvenance pkg

theorem CauchyNetWitnessCompleteSubwindow_carrier_restriction [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic
      restrictedClassifier restrictedReal restrictedTransport restrictedRoute
      restrictedProvenance restrictedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetWitnessCompleteSubwindow directed schedule regseq dyadic classifier realHandoff
        transport route provenance nameRow restrictedDirected restrictedSchedule
        restrictedRegseq restrictedDyadic restrictedClassifier restrictedReal restrictedTransport
        restrictedRoute restrictedProvenance restrictedName bundle pkg →
      CauchyNetCarrier restrictedDirected restrictedSchedule restrictedRegseq restrictedDyadic
          restrictedClassifier restrictedReal restrictedTransport restrictedRoute
          restrictedProvenance restrictedName bundle pkg ∧
        Cont restrictedRegseq restrictedReal restrictedRoute ∧
          PkgSig bundle restrictedProvenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro subwindow
  obtain ⟨_originalCarrier, restrictedCarrier, restrictedRouteHandoff,
    restrictedProvenancePkg⟩ := subwindow
  exact ⟨restrictedCarrier, restrictedRouteHandoff, restrictedProvenancePkg⟩

end BEDC.Derived.CauchyNetUp

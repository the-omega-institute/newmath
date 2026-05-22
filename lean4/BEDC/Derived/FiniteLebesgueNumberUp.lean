import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.Derived.FiniteLebesgueNumberUp.BridgePacketExactness
import BEDC.Derived.FiniteLebesgueNumberUp.L10PhaseConsumerReadiness
import BEDC.Derived.FiniteLebesgueNumberUp.L10SiblingRoute
import BEDC.Derived.FiniteLebesgueNumberUp.CompactContinuousSourceAccountability
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusWindowNoExtraSource
import BEDC.Derived.FiniteLebesgueNumberUp.RootRoutes
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusCover
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusConsumerDeterminacy
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusWindowAdmission
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseRadiusWindowExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusWindowSourceLock
import BEDC.Derived.FiniteLebesgueNumberUp.RootRadiusCoherencePackage
import BEDC.Derived.FiniteLebesgueNumberUp.RootTailRadiusSourcePackage
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseRootUnblockObligations
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseNonchoiceCover
import BEDC.Derived.FiniteLebesgueNumberUp.RealPhaseSourceExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.RealSourceNonchoice
import BEDC.Derived.FiniteLebesgueNumberUp.RootUnblockTerminalPackage
import BEDC.Derived.FiniteLebesgueNumberUp.TerminalReadiness
import BEDC.Derived.FiniteLebesgueNumberUp.SelectedTailBridgeLedger
import BEDC.Derived.FiniteLebesgueNumberUp.SelectedTailModulusExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.TailRadiusAdmission
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusConsumerNonescape

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberChoiceFreeTailRadiusLedger_certificate [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail realTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh tailAdmission
        streamTail regularTail realTail transport route provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row realTail ∧
              FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
                tailAdmission streamTail regularTail realTail transport route provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row realTail ∧ Cont window radius tailAdmission ∧
              Cont tailAdmission mesh streamTail ∧ Cont streamTail route regularTail ∧
                Cont regularTail nameRow realTail)
          (fun row : BHist => hsame row realTail ∧ PkgSig bundle realTail pkg)
          hsame ∧
        UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧
          UnaryHistory regularTail ∧ UnaryHistory realTail ∧
            Cont window radius tailAdmission ∧ Cont tailAdmission mesh streamTail ∧
              Cont streamTail route regularTail ∧ Cont regularTail nameRow realTail ∧
                PkgSig bundle realTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh tailAdmission
        streamTail regularTail realTail transport route provenance nameRow bundle pkg :=
    ledger
  obtain ⟨carrier, windowRadiusTail, tailMeshStream, streamRouteRegular,
    regularNameReal, _provenancePkg, realPkg⟩ := ledger
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailAdmission :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamTail :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realTail :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have sourceReal :
      (fun row : BHist =>
        hsame row realTail ∧
          FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
            tailAdmission streamTail regularTail realTail transport route provenance
            nameRow bundle pkg) realTail := by
    exact ⟨hsame_refl realTail, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realTail ∧
              FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
                tailAdmission streamTail regularTail realTail transport route provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row realTail ∧ Cont window radius tailAdmission ∧
              Cont tailAdmission mesh streamTail ∧ Cont streamTail route regularTail ∧
                Cont regularTail nameRow realTail)
          (fun row : BHist => hsame row realTail ∧ PkgSig bundle realTail pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realTail sourceReal
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, windowRadiusTail, tailMeshStream, streamRouteRegular,
            regularNameReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact
    ⟨cert, tailUnary, streamUnary, regularUnary, realUnary, windowRadiusTail,
      tailMeshStream, streamRouteRegular, regularNameReal, realPkg⟩

def FiniteLebesgueNumberCompactContinuousUnblockLedger [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow compactRead continuousRead
      uniformRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont radius mesh compactRead ∧ Cont compactRead route continuousRead ∧
      Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg

theorem FiniteLebesgueNumberCompactContinuousUnblockLedger_certificate [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead continuousRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh transport
        route provenance nameRow compactRead continuousRead uniformRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
                transport route provenance nameRow compactRead continuousRead uniformRead
                bundle pkg)
          (fun row : BHist =>
            hsame row uniformRead ∧ Cont radius mesh compactRead ∧
              Cont compactRead route continuousRead ∧
                Cont continuousRead nameRow uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame ∧
        UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
          UnaryHistory uniformRead ∧ Cont radius mesh compactRead ∧
            Cont compactRead route continuousRead ∧
              Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh transport
        route provenance nameRow compactRead continuousRead uniformRead bundle pkg :=
    ledger
  obtain ⟨carrier, radiusMeshCompact, compactRouteContinuous, continuousNameUniform,
    uniformPkg⟩ := ledger
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist =>
        hsame row uniformRead ∧
          FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
            transport route provenance nameRow compactRead continuousRead uniformRead
            bundle pkg) uniformRead := by
    exact ⟨hsame_refl uniformRead, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
                transport route provenance nameRow compactRead continuousRead uniformRead
                bundle pkg)
          (fun row : BHist =>
            hsame row uniformRead ∧ Cont radius mesh compactRead ∧
              Cont compactRead route continuousRead ∧
                Cont continuousRead nameRow uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, radiusMeshCompact, compactRouteContinuous,
            continuousNameUniform⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, compactUnary, continuousUnary, uniformUnary, radiusMeshCompact,
      compactRouteContinuous, continuousNameUniform, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp

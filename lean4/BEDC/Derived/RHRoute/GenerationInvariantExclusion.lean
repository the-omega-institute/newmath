import BEDC.Derived.RHRoute.SpectralRigidityRoute

namespace BEDC.Derived.RHRoute.GenerationInvariantExclusion

open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.SpectralRigidityRoute

universe u v

abbrev TraceEvent :=
  BEDC.Derived.RHRoute.RecursiveTower.TraceEvent

/-!
生成不变量路线只处理闭生成载体上的归纳事实。边界输入放在
`Boundary` 命名空间中；这些字段是路线条件, 不是 RH 证明。
-/

structure GenerationInvariantRules
    {signature : RHFreeZeroSignature}
    (stable : GeneratedZero signature -> Prop) where
  primeLocal :
    (window : PrimeWindow) -> (p : Nat) -> (member : window.mem p) ->
      stable (GeneratedZero.primeLocal window p member)
  functionalMirror :
    (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.functionalMirror z)
  conjugationTransport :
    (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.conjugationTransport z)
  classifierTransport :
    (tag : Nat) -> (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.classifierTransport tag z)
  analyticGlue :
    (left right : GeneratedZero signature) ->
      stable left -> stable right ->
        stable (GeneratedZero.analyticGlue left right)
  compatibleLimitSeal :
    (fuel : Nat) -> (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.compatibleLimitSeal fuel z)
  ledgerReplay :
    (z : GeneratedZero signature) -> (trace : List TraceEvent) ->
      stable z -> stable (GeneratedZero.ledgerReplay z trace)
  finiteWindowClose :
    (window : PrimeWindow) -> (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.finiteWindowClose window z)
  recursiveTowerReadback :
    (event : TraceEvent) -> (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.recursiveTowerReadback event z)
  nonCollapseGuard :
    (budget : Nat) -> (z : GeneratedZero signature) ->
      stable z -> stable (GeneratedZero.nonCollapseGuard budget z)

theorem generationInvariantRules_cover
    {signature : RHFreeZeroSignature}
    {stable : GeneratedZero signature -> Prop}
    (rules : GenerationInvariantRules stable) :
    (z : GeneratedZero signature) -> stable z := by
  intro z
  induction z with
  | primeLocal window p member =>
      exact rules.primeLocal window p member
  | functionalMirror z ih =>
      exact rules.functionalMirror z ih
  | conjugationTransport z ih =>
      exact rules.conjugationTransport z ih
  | classifierTransport tag z ih =>
      exact rules.classifierTransport tag z ih
  | analyticGlue left right ihLeft ihRight =>
      exact rules.analyticGlue left right ihLeft ihRight
  | compatibleLimitSeal fuel z ih =>
      exact rules.compatibleLimitSeal fuel z ih
  | ledgerReplay z trace ih =>
      exact rules.ledgerReplay z trace ih
  | finiteWindowClose window z ih =>
      exact rules.finiteWindowClose window z ih
  | recursiveTowerReadback event z ih =>
      exact rules.recursiveTowerReadback event z ih
  | nonCollapseGuard budget z ih =>
      exact rules.nonCollapseGuard budget z ih

def generationInvariantAlgebra
    {signature : RHFreeZeroSignature}
    {stable : GeneratedZero signature -> Prop}
    (rules : GenerationInvariantRules stable) :
    ZeroAlgebra signature (PSigma (fun z : GeneratedZero signature => stable z)) where
  alg
    | ZeroSigF.primeLocal window p member =>
        PSigma.mk (GeneratedZero.primeLocal window p member)
          (rules.primeLocal window p member)
    | ZeroSigF.functionalMirror z =>
        PSigma.mk (GeneratedZero.functionalMirror z.1)
          (rules.functionalMirror z.1 z.2)
    | ZeroSigF.conjugationTransport z =>
        PSigma.mk (GeneratedZero.conjugationTransport z.1)
          (rules.conjugationTransport z.1 z.2)
    | ZeroSigF.classifierTransport tag z =>
        PSigma.mk (GeneratedZero.classifierTransport tag z.1)
          (rules.classifierTransport tag z.1 z.2)
    | ZeroSigF.analyticGlue left right =>
        PSigma.mk (GeneratedZero.analyticGlue left.1 right.1)
          (rules.analyticGlue left.1 right.1 left.2 right.2)
    | ZeroSigF.compatibleLimitSeal fuel z =>
        PSigma.mk (GeneratedZero.compatibleLimitSeal fuel z.1)
          (rules.compatibleLimitSeal fuel z.1 z.2)
    | ZeroSigF.ledgerReplay z trace =>
        PSigma.mk (GeneratedZero.ledgerReplay z.1 trace)
          (rules.ledgerReplay z.1 trace z.2)
    | ZeroSigF.finiteWindowClose window z =>
        PSigma.mk (GeneratedZero.finiteWindowClose window z.1)
          (rules.finiteWindowClose window z.1 z.2)
    | ZeroSigF.recursiveTowerReadback event z =>
        PSigma.mk (GeneratedZero.recursiveTowerReadback event z.1)
          (rules.recursiveTowerReadback event z.1 z.2)
    | ZeroSigF.nonCollapseGuard budget z =>
        PSigma.mk (GeneratedZero.nonCollapseGuard budget z.1)
          (rules.nonCollapseGuard budget z.1 z.2)

theorem generationInvariantAlgebra_readback
    {signature : RHFreeZeroSignature}
    {stable : GeneratedZero signature -> Prop}
    (rules : GenerationInvariantRules stable)
    (z : GeneratedZero signature) :
    (GeneratedZero.fold (generationInvariantAlgebra rules) z).1 = z := by
  induction z with
  | primeLocal window p member =>
      rfl
  | functionalMirror z ih =>
      exact congrArg GeneratedZero.functionalMirror ih
  | conjugationTransport z ih =>
      exact congrArg GeneratedZero.conjugationTransport ih
  | classifierTransport tag z ih =>
      exact congrArg (GeneratedZero.classifierTransport tag) ih
  | analyticGlue left right ihLeft ihRight =>
      change GeneratedZero.analyticGlue
        (GeneratedZero.fold (generationInvariantAlgebra rules) left).1
        (GeneratedZero.fold (generationInvariantAlgebra rules) right).1 =
          GeneratedZero.analyticGlue left right
      rw [ihLeft, ihRight]
  | compatibleLimitSeal fuel z ih =>
      exact congrArg (GeneratedZero.compatibleLimitSeal fuel) ih
  | ledgerReplay z trace ih =>
      exact congrArg (fun w => GeneratedZero.ledgerReplay w trace) ih
  | finiteWindowClose window z ih =>
      exact congrArg (GeneratedZero.finiteWindowClose window) ih
  | recursiveTowerReadback event z ih =>
      exact congrArg (GeneratedZero.recursiveTowerReadback event) ih
  | nonCollapseGuard budget z ih =>
      exact congrArg (GeneratedZero.nonCollapseGuard budget) ih

def generatedInvariantInitialitySigma
    {signature : RHFreeZeroSignature}
    {stable : GeneratedZero signature -> Prop}
    (rules : GenerationInvariantRules stable)
    (z : GeneratedZero signature) :
    PSigma (fun w : GeneratedZero signature => w = z ∧ stable w) :=
  let folded := GeneratedZero.fold (generationInvariantAlgebra rules) z
  PSigma.mk folded.1
    (And.intro (generationInvariantAlgebra_readback rules z) folded.2)

theorem generatedInvariantInitialitySigma_stable
    {signature : RHFreeZeroSignature}
    {stable : GeneratedZero signature -> Prop}
    (rules : GenerationInvariantRules stable)
    (z : GeneratedZero signature) :
    stable (generatedInvariantInitialitySigma rules z).1 :=
  (generatedInvariantInitialitySigma rules z).2.right

structure GenerationInvariantData (signature : RHFreeZeroSignature) where
  stable : GeneratedZero signature -> Prop
  rules : GenerationInvariantRules stable

def generationInvariantData_cover
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature)
    (z : GeneratedZero signature) : data.stable z :=
  generationInvariantRules_cover data.rules z

def generatedInvariantSigma
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature)
    (z : GeneratedZero signature) :
    PSigma (fun w : GeneratedZero signature => w = z ∧ data.stable w) :=
  PSigma.mk z (And.intro rfl (generationInvariantData_cover data z))

theorem generatedInvariantSigma_readback
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature)
    (z : GeneratedZero signature) :
    (generatedInvariantSigma data z).1 = z := by
  rfl

theorem generatedInvariantSigma_stable
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature)
    (z : GeneratedZero signature) :
    data.stable (generatedInvariantSigma data z).1 :=
  (generatedInvariantSigma data z).2.right

structure ExcludedGeneratedZeroConfig
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature) where
  generated : GeneratedZero signature
  invariant_refutes : data.stable generated -> False

theorem generationInvariant_excludes_config
    {signature : RHFreeZeroSignature}
    {data : GenerationInvariantData signature}
    (config : ExcludedGeneratedZeroConfig data) : False := by
  exact config.invariant_refutes
    (generationInvariantData_cover data config.generated)

namespace Boundary

structure DefectInvariantLink
    (I : PrimeSkewDefectInterface.{u, v})
    {signature : RHFreeZeroSignature}
    (data : GenerationInvariantData signature) where
  generatedOfAtom :
    (x : I.bulk) -> I.zero_atom x -> GeneratedZero signature
  defectContradictsInvariant :
    (x : I.bulk) -> (zero : I.zero_atom x) ->
      data.stable (generatedOfAtom x zero) ->
        PrimeDefect I.bulk x -> False

theorem defectInvariantLink_to_primeDefectZeroIncompatibility
    {I : PrimeSkewDefectInterface.{u, v}}
    {signature : RHFreeZeroSignature}
    {data : GenerationInvariantData signature}
    (link : DefectInvariantLink I data) :
    PrimeDefectZeroIncompatibility I := by
  intro x zero defect
  exact link.defectContradictsInvariant x zero
    (generationInvariantData_cover data (link.generatedOfAtom x zero))
    defect

def defectInvariantLink_to_globalSpectralRigidity
    {I : PrimeSkewDefectInterface.{u, v}}
    {signature : RHFreeZeroSignature}
    {data : GenerationInvariantData signature}
    (faithful : BoundaryFaithfulness I)
    (link : DefectInvariantLink I data) :
    GlobalSpectralRigidity I where
  boundary_faithfulness := faithful
  defect_zero_incompatibility :=
    defectInvariantLink_to_primeDefectZeroIncompatibility link

theorem defectInvariantLink_excludes_off_line
    {I : PrimeSkewDefectInterface.{u, v}}
    {signature : RHFreeZeroSignature}
    {data : GenerationInvariantData signature}
    (link : DefectInvariantLink I data)
    (obligation : OffLineZeroBoundaryObligation I)
    (faithful : BoundaryFaithfulness I)
    (zero : obligation.off_line_zero) : False := by
  exact offLineBoundary_defect_zero_incompatible obligation faithful
    (defectInvariantLink_to_primeDefectZeroIncompatibility link) zero

end Boundary

structure GenerationInvariantExclusionRoute
    (I : PrimeSkewDefectInterface.{u, v}) where
  signature : RHFreeZeroSignature
  invariant : GenerationInvariantData signature
  boundary_link : Boundary.DefectInvariantLink I invariant
  off_line_boundary : OffLineZeroBoundaryObligation I
  boundary_faithfulness : BoundaryFaithfulness I

def GenerationInvariantExclusionRoute.globalRigidity
    {I : PrimeSkewDefectInterface.{u, v}}
    (route : GenerationInvariantExclusionRoute I) :
    GlobalSpectralRigidity I :=
  Boundary.defectInvariantLink_to_globalSpectralRigidity
    route.boundary_faithfulness route.boundary_link

theorem generationInvariantRoute_excludes_off_line
    {I : PrimeSkewDefectInterface.{u, v}}
    (route : GenerationInvariantExclusionRoute I)
    (zero : route.off_line_boundary.off_line_zero) : False := by
  exact globalSpectralRigidity_excludes_off_line route.off_line_boundary
    route.globalRigidity zero

theorem conditionalGenerationInvariant_excludes_off_line
    {I : PrimeSkewDefectInterface.{u, v}}
    {signature : RHFreeZeroSignature}
    {data : GenerationInvariantData signature}
    (link : Boundary.DefectInvariantLink I data)
    (obligation : OffLineZeroBoundaryObligation I)
    (faithful : BoundaryFaithfulness I)
    (zero : obligation.off_line_zero) : False := by
  exact Boundary.defectInvariantLink_excludes_off_line link obligation
    faithful zero

end BEDC.Derived.RHRoute.GenerationInvariantExclusion

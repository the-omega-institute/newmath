import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FunctionalEquationSymmetry
import BEDC.Derived.RHRoute.WeilPositivityRoute
import BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure
import BEDC.Real.RatNumLogEnclosure

namespace BEDC.Derived.RHRoute.CausalReflectionPositiveCone

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.WeilPositivityRoute
open BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

def ratComplexOfRat (q : Rat) : RatComplex :=
  { re := q, im := ratZero }

structure InnerProductCarrier where
  H : Type
  inner : H -> H -> RatComplex
  normSq : H -> Rat
  normSq_nonnegative : ∀ x : H, ratLe ratZero (normSq x)
  inner_self_reads_normSq :
    ∀ x : H, RatComplexEq (inner x x) (ratComplexOfRat (normSq x))
  linearCombination : List (RatComplex × H) -> H

structure ContractionSemigroupField
    (carrier : InnerProductCarrier) where
  time : Type
  nonnegative_time : time -> Prop
  T : time -> carrier.H -> carrier.H
  contractive :
    ∀ t : time, nonnegative_time t ->
      ∀ x : carrier.H, ratLe (carrier.normSq (T t x)) (carrier.normSq x)
  causalAdmissible : carrier.H -> Prop
  causal_stable :
    ∀ t : time, nonnegative_time t ->
      ∀ x : carrier.H, causalAdmissible x -> causalAdmissible (T t x)

structure AntiunitaryField
    (carrier : InnerProductCarrier)
    (flow : ContractionSemigroupField carrier) where
  J : carrier.H -> carrier.H
  adjointT : flow.time -> carrier.H -> carrier.H
  antiunitary_readback : Prop

structure EntireField where
  E : RatComplex -> RatComplex
  Esharp : RatComplex -> RatComplex
  A_E : RatComplex -> RatComplex
  K_E : RatComplex -> RatComplex -> RatComplex
  HermiteBiehler : Prop
  allZerosReal : Prop

structure EntireXiReadback (entire : EntireField) where
  Xi : RatComplex -> RatComplex
  A_E_reads_Xi :
    ∀ z : RatComplex, RatComplexEq (entire.A_E z) (Xi z)
  zero_readback_scope : Prop

structure KernelGramPacket where
  terms : List (RatComplex × RatComplex)

def KernelGramPacket.carrierTerms
    (carrier : InnerProductCarrier)
    (eta : RatComplex -> carrier.H)
    (packet : KernelGramPacket) :
    List (RatComplex × carrier.H) :=
  packet.terms.map (fun term => (term.fst, eta term.snd))

def gramVector
    (carrier : InnerProductCarrier)
    (eta : RatComplex -> carrier.H)
    (packet : KernelGramPacket) : carrier.H :=
  carrier.linearCombination (packet.carrierTerms carrier eta)

def kernelQuadratic
    (carrier : InnerProductCarrier)
    (eta : RatComplex -> carrier.H)
    (packet : KernelGramPacket) : Rat :=
  carrier.normSq (gramVector carrier eta packet)

def KernelPositive
    (carrier : InnerProductCarrier)
    (eta : RatComplex -> carrier.H) : Prop :=
  ∀ packet : KernelGramPacket,
    ratLe ratZero (kernelQuadratic carrier eta packet)

def KernelEq
    (carrier : InnerProductCarrier)
    (entire : EntireField)
    (eta : RatComplex -> carrier.H) : Prop :=
  ∀ z w : RatComplex,
    RatComplexEq (entire.K_E z w) (carrier.inner (eta w) (eta z))

structure DensityBridge
    (carrier : InnerProductCarrier)
    (B : RatTestFunction -> carrier.H)
    (eta : RatComplex -> carrier.H) where
  test_image_dense : Prop
  eta_in_test_closure : Prop

inductive CRPCHardCoreProjection where
  | analyticBridgeO1
  | weilSosO2
  | deBrangesKernelO3

inductive CRPCProjectionSurface where
  | constructiveRH
  | weilPositivity
  | hermiteBiehlerKernel
  | unitaryScale
  | iotaSymmetry

def hardCoreProjections : List CRPCHardCoreProjection :=
  [ CRPCHardCoreProjection.analyticBridgeO1,
    CRPCHardCoreProjection.weilSosO2,
    CRPCHardCoreProjection.deBrangesKernelO3 ]

def masterProjectionSurfaces : List CRPCProjectionSurface :=
  [ CRPCProjectionSurface.constructiveRH,
    CRPCProjectionSurface.weilPositivity,
    CRPCProjectionSurface.hermiteBiehlerKernel,
    CRPCProjectionSurface.unitaryScale,
    CRPCProjectionSurface.iotaSymmetry ]

inductive CRPCInhabitantFrontierObligation where
  | primeArchimedeanCausalFlowConstruction
  | boundaryDeterminantXiReadback
  | noZeroLocationInput

def canonicalInhabitantFrontierObligations :
    List CRPCInhabitantFrontierObligation :=
  [ CRPCInhabitantFrontierObligation.primeArchimedeanCausalFlowConstruction,
    CRPCInhabitantFrontierObligation.boundaryDeterminantXiReadback,
    CRPCInhabitantFrontierObligation.noZeroLocationInput ]

structure CausalReflectionPositiveCone where
  H : InnerProductCarrier
  T : ContractionSemigroupField H
  J : AntiunitaryField H T
  J_invol : ∀ x : H.H, J.J (J.J x) = x
  J_time :
    ∀ t : T.time, T.nonnegative_time t ->
      ∀ x : H.H, J.J (T.T t (J.J x)) = J.adjointT t x
  v : H.H
  B : RatTestFunction -> H.H
  B_causal : ∀ f : RatTestFunction, T.causalAdmissible (B f)
  E : EntireField
  E_xi : EntireXiReadback E
  eta : RatComplex -> H.H
  kernel_eq : KernelEq H E eta
  weilFunctional : FullWeilFunctional
  weil_eq :
    ∀ g : RatTestAlgebraElement,
      RatEq
        (weilFunctional.value g.test.quadraticArgument)
        (H.normSq (B g.test))
  iotaTest : RatTestFunction -> RatTestFunction
  iota_ok : ∀ f : RatTestFunction, B (iotaTest f) = J.J (B f)
  density : DensityBridge H B eta
  HB_of_kernel_pos :
    KernelEq H E eta -> KernelPositive H eta -> E.HermiteBiehler
  real_zeros_of_HB :
    E.HermiteBiehler -> E.allZerosReal
  constructive_rh_of_E_xi_real_zeros :
    EntireXiReadback E -> E.allZerosReal -> ConstructiveRH
  unitaryScaleProjection : ZetaUnitaryScaleClosure
  inhabitant_frontier_obligations :
    List CRPCInhabitantFrontierObligation
  inhabitant_frontier_scope :
    inhabitant_frontier_obligations =
      canonicalInhabitantFrontierObligations

theorem hard_core_projection_count :
    hardCoreProjections.length = 3 := by
  rfl

theorem master_projection_surface_count :
    masterProjectionSurfaces.length = 5 := by
  rfl

theorem positive_of_gram
    (C : CausalReflectionPositiveCone) :
    KernelPositive C.H C.eta := by
  intro packet
  exact C.H.normSq_nonnegative (gramVector C.H C.eta packet)

theorem crpc_kernel_positive
    (C : CausalReflectionPositiveCone) :
    KernelPositive C.H C.eta :=
  positive_of_gram C

theorem CRPC_implies_RH
    (C : CausalReflectionPositiveCone) :
    ConstructiveRH := by
  have kernelPositive : KernelPositive C.H C.eta :=
    positive_of_gram C
  have hb : C.E.HermiteBiehler :=
    C.HB_of_kernel_pos C.kernel_eq kernelPositive
  have zerosReal : C.E.allZerosReal :=
    C.real_zeros_of_HB hb
  exact C.constructive_rh_of_E_xi_real_zeros C.E_xi zerosReal

theorem crpc_gives_weil_positivity
    (C : CausalReflectionPositiveCone) :
    GlobalWeilPositivity C.weilFunctional := by
  intro g
  have normNonnegative :
      ratLe ratZero (C.H.normSq (C.B g.test)) :=
    C.H.normSq_nonnegative (C.B g.test)
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right normNonnegative
    (RatEq_symm (C.weil_eq g))

def crpc_gives_unitary_scale
    (C : CausalReflectionPositiveCone) :
    ZetaUnitaryScaleClosure :=
  C.unitaryScaleProjection

def IotaSymmetryCompatible
    (C : CausalReflectionPositiveCone) : Prop :=
  ∀ f : RatTestFunction, C.B (C.iotaTest f) = C.J.J (C.B f)

theorem crpc_gives_iota_symmetry
    (C : CausalReflectionPositiveCone) :
    IotaSymmetryCompatible C :=
  C.iota_ok

def crpc_gives_analytic_bridge_O1
    (C : CausalReflectionPositiveCone) :
    EntireXiReadback C.E :=
  C.E_xi

theorem crpc_gives_weil_sos_O2
    (C : CausalReflectionPositiveCone) :
    ∀ g : RatTestAlgebraElement,
      RatEq
        (C.weilFunctional.value g.test.quadraticArgument)
        (C.H.normSq (C.B g.test)) :=
  C.weil_eq

theorem crpc_gives_kernel_gram_O3
    (C : CausalReflectionPositiveCone) :
    ∀ packet : KernelGramPacket,
      ratLe ratZero (kernelQuadratic C.H C.eta packet) :=
  positive_of_gram C

theorem crpc_gives_kernel_eq_O3
    (C : CausalReflectionPositiveCone) :
    ∀ z w : RatComplex,
      RatComplexEq (C.E.K_E z w) (C.H.inner (C.eta w) (C.eta z)) :=
  C.kernel_eq

theorem crpc_inhabitant_frontier_obligation_count
    (C : CausalReflectionPositiveCone) :
    C.inhabitant_frontier_obligations.length = 3 := by
  rw [C.inhabitant_frontier_scope]
  rfl

end BEDC.Derived.RHRoute.CausalReflectionPositiveCone

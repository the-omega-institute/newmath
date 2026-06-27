import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.ZeroSignatureFaithfulness

open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u

def ZeroSignatureCarrierMapFaithful {signature : RHFreeZeroSignature}
    (f : GeneratedZero signature -> GeneratedZero signature) : Prop :=
  ∀ z w : GeneratedZero signature, f z = f w -> z = w

def zeroSignatureCarrierMap (signature : RHFreeZeroSignature) :
    GeneratedZero signature -> GeneratedZero signature :=
  GeneratedZero.fold (generatedZeroAlgebra signature)

theorem zeroSignatureCarrierMap_hom (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (generatedZeroAlgebra signature)
      (zeroSignatureCarrierMap signature) := by
  exact (generatedZero_initiality (generatedZeroAlgebra signature)).left

theorem generatedZero_identity_hom (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (generatedZeroAlgebra signature)
      (fun z : GeneratedZero signature => z) := by
  intro op
  cases op <;> rfl

theorem zeroSignatureCarrierMap_unique (signature : RHFreeZeroSignature)
    (f : GeneratedZero signature -> GeneratedZero signature)
    (hom : IsZeroAlgebraHom (generatedZeroAlgebra signature) f) :
    ∀ z : GeneratedZero signature, f z = zeroSignatureCarrierMap signature z := by
  exact (generatedZero_initiality (generatedZeroAlgebra signature)).right f hom

theorem zeroSignatureCarrierMap_identity (signature : RHFreeZeroSignature) :
    ∀ z : GeneratedZero signature, zeroSignatureCarrierMap signature z = z := by
  intro z
  exact Eq.symm
    (zeroSignatureCarrierMap_unique signature
      (fun x : GeneratedZero signature => x)
      (generatedZero_identity_hom signature) z)

theorem zeroSignatureCarrierMap_faithful (signature : RHFreeZeroSignature) :
    ZeroSignatureCarrierMapFaithful (zeroSignatureCarrierMap signature) := by
  intro z w same
  rw [zeroSignatureCarrierMap_identity signature z,
    zeroSignatureCarrierMap_identity signature w] at same
  exact same

def signatureConstructorCodes (signature : RHFreeZeroSignature) : List Nat :=
  signature.constructors.map zeroConstructorKindCode

def generatedZeroShapeCodes {signature : RHFreeZeroSignature} :
    GeneratedZero signature -> List Nat
  | GeneratedZero.primeLocal _ _ _ =>
      [zeroConstructorKindCode ZeroConstructorKind.primeLocal]
  | GeneratedZero.functionalMirror z =>
      zeroConstructorKindCode ZeroConstructorKind.functionalMirror ::
        generatedZeroShapeCodes z
  | GeneratedZero.conjugationTransport z =>
      zeroConstructorKindCode ZeroConstructorKind.conjugationTransport ::
        generatedZeroShapeCodes z
  | GeneratedZero.classifierTransport _ z =>
      zeroConstructorKindCode ZeroConstructorKind.classifierTransport ::
        generatedZeroShapeCodes z
  | GeneratedZero.analyticGlue left right =>
      zeroConstructorKindCode ZeroConstructorKind.analyticGlue ::
        (generatedZeroShapeCodes left ++ generatedZeroShapeCodes right)
  | GeneratedZero.compatibleLimitSeal _ z =>
      zeroConstructorKindCode ZeroConstructorKind.compatibleLimitSeal ::
        generatedZeroShapeCodes z
  | GeneratedZero.ledgerReplay z _ =>
      zeroConstructorKindCode ZeroConstructorKind.ledgerReplay ::
        generatedZeroShapeCodes z
  | GeneratedZero.finiteWindowClose _ z =>
      zeroConstructorKindCode ZeroConstructorKind.finiteWindowClose ::
        generatedZeroShapeCodes z
  | GeneratedZero.recursiveTowerReadback _ z =>
      zeroConstructorKindCode ZeroConstructorKind.recursiveTowerReadback ::
        generatedZeroShapeCodes z
  | GeneratedZero.nonCollapseGuard _ z =>
      zeroConstructorKindCode ZeroConstructorKind.nonCollapseGuard ::
        generatedZeroShapeCodes z

structure SignatureGeneratedZeroPoint where
  signature_codes : List Nat
  zero_shape_codes : List Nat

def zeroSignatureGeneratedPoint {signature : RHFreeZeroSignature}
    (z : GeneratedZero signature) : SignatureGeneratedZeroPoint where
  signature_codes := signatureConstructorCodes signature
  zero_shape_codes := generatedZeroShapeCodes z

def SignatureCodesSeparated (left right : RHFreeZeroSignature) : Prop :=
  signatureConstructorCodes left ≠ signatureConstructorCodes right

theorem zeroSignatureGeneratedPoint_reads_signature
    {signature : RHFreeZeroSignature} (z : GeneratedZero signature) :
    (zeroSignatureGeneratedPoint z).signature_codes =
      signatureConstructorCodes signature := by
  rfl

theorem different_signatures_generate_different_zero_points
    {left right : RHFreeZeroSignature}
    (different : SignatureCodesSeparated left right) :
    ∀ (z : GeneratedZero left) (w : GeneratedZero right),
      zeroSignatureGeneratedPoint z ≠ zeroSignatureGeneratedPoint w := by
  intro z w samePoint
  have sameCodes :
      (zeroSignatureGeneratedPoint z).signature_codes =
        (zeroSignatureGeneratedPoint w).signature_codes := by
    rw [samePoint]
  exact different sameCodes

theorem rhFreeZeroSignature_code_readback :
    signatureConstructorCodes rhFreeZeroSignature =
      rhFreeZeroSignatureKinds.map zeroConstructorKindCode := by
  rfl

end BEDC.Derived.RHRoute.ZeroSignatureFaithfulness

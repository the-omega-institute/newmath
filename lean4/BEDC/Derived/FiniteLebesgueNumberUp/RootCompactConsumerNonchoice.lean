import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootCompactConsumerNonchoice [AskSetup] [PackageSetup]
    {cover mesh radius stream regseq real provenance name compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover mesh radius stream regseq real provenance name
        bundle pkg ->
      Cont cover mesh radius ->
        Cont radius stream regseq ->
          Cont regseq real compactRead ->
            PkgSig bundle compactRead pkg ->
              UnaryHistory cover ∧ UnaryHistory mesh ∧ UnaryHistory radius ∧
                UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory compactRead ∧
                  Cont cover mesh radius ∧ Cont radius stream regseq ∧
                    Cont regseq real compactRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: FiniteLebesgueNumberCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverMeshRadius radiusStreamRegseq regseqRealCompact compactPkg
  obtain ⟨coverUnary, meshUnary, _radiusUnary, streamUnary, _regseqUnary, realUnary,
    _provenanceUnary, _nameUnary, _coverMeshRadius, _radiusStreamRegseq,
    _realNameProvenance, namePkg⟩ := carrier
  have radiusUnary : UnaryHistory radius :=
    unary_cont_closed coverUnary meshUnary coverMeshRadius
  have regseqUnaryFromRoute : UnaryHistory regseq :=
    unary_cont_closed radiusUnary streamUnary radiusStreamRegseq
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed regseqUnaryFromRoute realUnary regseqRealCompact
  exact
    ⟨coverUnary, meshUnary, radiusUnary, streamUnary, regseqUnaryFromRoute,
      compactReadUnary, coverMeshRadius, radiusStreamRegseq, regseqRealCompact,
      namePkg, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp

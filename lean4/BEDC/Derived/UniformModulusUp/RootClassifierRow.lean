import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_root_classifier_row [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead foldedExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead foldLedger foldedExport ->
              PkgSig bundle foldedExport pkg ->
                UnaryHistory compactRead ∧ UnaryHistory pointwiseRead ∧
                  UnaryHistory foldLedger ∧ UnaryHistory foldedExport ∧
                    Cont bundleRow radius compactRead ∧
                      Cont compactRead pointwise pointwiseRead ∧
                        Cont pointwiseRead foldLedger foldedExport ∧
                          Cont precision radius foldLedger ∧
                            PkgSig bundle foldedExport pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet pointwiseUnary compactRoute pointwiseRoute foldedRoute foldedPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    _coverageRoute, _transportRoute, precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have foldedExportUnary : UnaryHistory foldedExport :=
    unary_cont_closed pointwiseReadUnary foldLedgerUnary foldedRoute
  exact
    ⟨compactReadUnary, pointwiseReadUnary, foldLedgerUnary, foldedExportUnary,
      compactRoute, pointwiseRoute, foldedRoute, precisionRadiusFoldLedger, foldedPkg⟩

end BEDC.Derived.UniformModulusUp

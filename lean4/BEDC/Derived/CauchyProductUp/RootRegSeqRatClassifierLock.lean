import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_regseqrat_classifier_lock [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes regseqSeal →
        PkgSig bundle regseqSeal pkg →
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
            UnaryHistory radiusB ∧ UnaryHistory observationA ∧ UnaryHistory observationB ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
                Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                  Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle regseqSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesRegseq regseqPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRegseq
  exact
    ⟨windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, observationAUnary,
      observationBUnary, productUnary, classifierUnary, regseqUnary, windowTransport,
      productRoute, classifierRoute, classifierRoutesRegseq, namePkg, regseqPkg⟩

end BEDC.Derived.CauchyProductUp

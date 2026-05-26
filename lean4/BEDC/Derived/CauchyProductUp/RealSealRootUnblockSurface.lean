import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_seal_root_unblock_surface [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes regseqSeal →
        Cont regseqSeal ledger realSeal →
          Cont realSeal routes budgetSeal →
            PkgSig bundle budgetSeal pkg →
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
                UnaryHistory realSeal ∧ UnaryHistory budgetSeal ∧
                  Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                    Cont regseqSeal ledger realSeal ∧ Cont realSeal routes budgetSeal ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRegseq regseqReal realBudget budgetPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqReal
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed realSealUnary routesUnary realBudget
  exact
    ⟨productUnary, classifierUnary, regseqSealUnary, realSealUnary, budgetSealUnary,
      classifierRoute, classifierRegseq, regseqReal, realBudget, namePkg, budgetPkg⟩

end BEDC.Derived.CauchyProductUp

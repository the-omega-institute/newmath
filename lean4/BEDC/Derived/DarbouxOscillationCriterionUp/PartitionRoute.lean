import BEDC.Derived.DarbouxOscillationCriterionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DarbouxOscillationCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DarbouxOscillationCriterionCarrier [AskSetup] [PackageSetup]
    (I S L U O M R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory I ∧ UnaryHistory S ∧ UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory O ∧
    UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont M S O ∧ Cont O R E ∧ Cont H C N ∧
        PkgSig bundle P pkg

theorem DarbouxOscillationCriterionPartitionRoute [AskSetup] [PackageSetup]
    {I S L U O M R E H C P N partitionRead oscillationRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DarbouxOscillationCriterionCarrier I S L U O M R E H C P N bundle pkg ->
      Cont M S partitionRead ->
        Cont partitionRead O oscillationRead ->
          Cont oscillationRead R regularRead ->
            Cont regularRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory M ∧ UnaryHistory partitionRead ∧ UnaryHistory oscillationRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ Cont M S partitionRead ∧
                    Cont partitionRead O oscillationRead ∧
                      Cont oscillationRead R regularRead ∧ Cont regularRead E sealRead ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier partitionRoute oscillationRoute regularRoute sealRoute sealPkg
  obtain ⟨_unaryI, unaryS, _unaryL, _unaryU, unaryO, unaryM, unaryR, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierPartition, _carrierSeal, _carrierName,
    _carrierPkg⟩ := carrier
  have unaryPartitionRead : UnaryHistory partitionRead :=
    unary_cont_closed unaryM unaryS partitionRoute
  have unaryOscillationRead : UnaryHistory oscillationRead :=
    unary_cont_closed unaryPartitionRead unaryO oscillationRoute
  have unaryRegularRead : UnaryHistory regularRead :=
    unary_cont_closed unaryOscillationRead unaryR regularRoute
  have unarySealRead : UnaryHistory sealRead :=
    unary_cont_closed unaryRegularRead unaryE sealRoute
  exact
    ⟨unaryM, unaryPartitionRead, unaryOscillationRead, unaryRegularRead, unarySealRead,
      partitionRoute, oscillationRoute, regularRoute, sealRoute, sealPkg⟩

end BEDC.Derived.DarbouxOscillationCriterionUp

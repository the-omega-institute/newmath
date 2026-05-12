import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoldenMeanShiftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GoldenMeanShiftCarrier [AskSetup] [PackageSetup]
    (window zero adjacency provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory zero ∧ UnaryHistory adjacency ∧
    UnaryHistory provenance ∧ UnaryHistory ledger ∧ Cont window adjacency ledger ∧
      PkgSig bundle provenance pkg

theorem GoldenMeanShiftCarrier_local_stability [AskSetup] [PackageSetup]
    {window zero adjacency provenance ledger window' zero' adjacency' provenance' ledger' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zero adjacency provenance ledger bundle pkg ->
      hsame window window' ->
        hsame zero zero' ->
          hsame adjacency adjacency' ->
            hsame provenance provenance' ->
              hsame ledger ledger' ->
                Cont window' adjacency' ledger' ->
                  PkgSig bundle provenance' pkg ->
                    GoldenMeanShiftCarrier window' zero' adjacency' provenance' ledger'
                        bundle pkg ∧
                      hsame ledger ledger' := by
  intro carrier sameWindow sameZero sameAdjacency sameProvenance sameLedger
    transportedCont transportedPkg
  obtain ⟨windowUnary, zeroUnary, adjacencyUnary, provenanceUnary, ledgerUnary,
    _ledgerCont, _provenancePkg⟩ := carrier
  exact
    ⟨⟨unary_transport windowUnary sameWindow,
        unary_transport zeroUnary sameZero,
        unary_transport adjacencyUnary sameAdjacency,
        unary_transport provenanceUnary sameProvenance,
        unary_transport ledgerUnary sameLedger,
        transportedCont,
        transportedPkg⟩,
      sameLedger⟩

end BEDC.Derived.GoldenMeanShiftUp

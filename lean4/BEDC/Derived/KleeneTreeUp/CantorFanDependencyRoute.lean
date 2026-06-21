import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp.CantorFanDependencyRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeCantorFanDependencyRoute [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport replay provenance localName
      cantorRead fanRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport replay provenance
        localName bundle pkg →
      Cont stream listSpine cantorRead →
        Cont cantorRead boolLedger fanRead →
          Cont fanRead obstruction obstructionRead →
            PkgSig bundle obstructionRead pkg →
              UnaryHistory cantorRead ∧ UnaryHistory fanRead ∧ UnaryHistory obstructionRead ∧
                Cont stream listSpine cantorRead ∧ Cont cantorRead boolLedger fanRead ∧
                  Cont fanRead obstruction obstructionRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: KleeneTreeCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier streamCantor cantorFan fanObstruction obstructionPkg
  obtain ⟨_treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have cantorUnary : UnaryHistory cantorRead :=
    unary_cont_closed streamUnary listUnary streamCantor
  have fanUnary : UnaryHistory fanRead :=
    unary_cont_closed cantorUnary boolUnary cantorFan
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed fanUnary obstructionUnary fanObstruction
  exact
    ⟨cantorUnary, fanUnary, obstructionReadUnary, streamCantor, cantorFan, fanObstruction,
      provenancePkg, obstructionPkg⟩

end BEDC.Derived.KleeneTreeUp.CantorFanDependencyRoute

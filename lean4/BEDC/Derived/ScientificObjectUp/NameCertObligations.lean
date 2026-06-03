import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ScientificObjectNameCertObligations [AskSetup] [PackageSetup]
    (R K I L B G A T O D H C P N recordRead classifierRead invariantRead ledgerRead
      bridgeRead truthRead openFitRead domainRead objectRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory R ∧ UnaryHistory K ∧ UnaryHistory I ∧ UnaryHistory L ∧ UnaryHistory B ∧
    UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory T ∧ UnaryHistory O ∧ UnaryHistory D ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont R K recordRead ∧ Cont K I classifierRead ∧
          Cont I L invariantRead ∧ Cont L B ledgerRead ∧ Cont B G bridgeRead ∧
            Cont T D truthRead ∧ Cont O D openFitRead ∧
              Cont truthRead domainRead objectRead ∧ PkgSig bundle objectRead pkg

theorem ScientificObjectNameCertObligations_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {R K I L B G A T O D H C P N recordRead classifierRead invariantRead ledgerRead
      bridgeRead truthRead openFitRead domainRead objectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScientificObjectNameCertObligations R K I L B G A T O D H C P N recordRead
        classifierRead invariantRead ledgerRead bridgeRead truthRead openFitRead domainRead
        objectRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            ScientificObjectNameCertObligations R K I L B G A T O D H C P N recordRead
              classifierRead invariantRead ledgerRead bridgeRead truthRead openFitRead
              domainRead objectRead bundle pkg ∧ hsame row objectRead)
          (fun row : BHist => hsame row objectRead)
          (fun row : BHist => hsame row objectRead ∧ PkgSig bundle objectRead pkg)
          hsame ∧
        UnaryHistory recordRead ∧ UnaryHistory classifierRead ∧
          UnaryHistory invariantRead ∧ UnaryHistory ledgerRead ∧
            UnaryHistory bridgeRead ∧ UnaryHistory truthRead ∧
              UnaryHistory openFitRead ∧ PkgSig bundle objectRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro obligations
  have obligationsAll := obligations
  obtain ⟨RUnary, KUnary, IUnary, LUnary, BUnary, GUnary, _AUnary, TUnary, OUnary,
    DUnary, _HUnary, _CUnary, _PUnary, _NUnary, recordRoute, classifierRoute,
    invariantRoute, ledgerRoute, bridgeRoute, truthRoute, openFitRoute, _objectRoute,
    objectPkg⟩ := obligations
  have recordUnary : UnaryHistory recordRead :=
    unary_cont_closed RUnary KUnary recordRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed KUnary IUnary classifierRoute
  have invariantUnary : UnaryHistory invariantRead :=
    unary_cont_closed IUnary LUnary invariantRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed LUnary BUnary ledgerRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed BUnary GUnary bridgeRoute
  have truthUnary : UnaryHistory truthRead :=
    unary_cont_closed TUnary DUnary truthRoute
  have openFitUnary : UnaryHistory openFitRead :=
    unary_cont_closed OUnary DUnary openFitRoute
  have source :
      (fun row : BHist =>
        ScientificObjectNameCertObligations R K I L B G A T O D H C P N recordRead
          classifierRead invariantRead ledgerRead bridgeRead truthRead openFitRead domainRead
          objectRead bundle pkg ∧ hsame row objectRead) objectRead := by
    exact ⟨obligationsAll, hsame_refl objectRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ScientificObjectNameCertObligations R K I L B G A T O D H C P N recordRead
              classifierRead invariantRead ledgerRead bridgeRead truthRead openFitRead
              domainRead objectRead bundle pkg ∧ hsame row objectRead)
          (fun row : BHist => hsame row objectRead)
          (fun row : BHist => hsame row objectRead ∧ PkgSig bundle objectRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro objectRead source
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows rowSource
        exact
          ⟨rowSource.left, hsame_trans (hsame_symm sameRows) rowSource.right⟩
    }
    pattern_sound := by
      intro _row rowSource
      exact rowSource.right
    ledger_sound := by
      intro _row rowSource
      exact ⟨rowSource.right, objectPkg⟩
  }
  exact
    ⟨cert, recordUnary, classifierUnary, invariantUnary, ledgerUnary, bridgeUnary,
      truthUnary, openFitUnary, objectPkg⟩

end BEDC.Derived.ScientificObjectUp

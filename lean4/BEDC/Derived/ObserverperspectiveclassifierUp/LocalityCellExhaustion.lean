import BEDC.Derived.ObserverperspectiveclassifierUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierLocalityCellExhaustion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance
      name localityRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality transport localityRead →
        Cont localityRead name witnessRead →
          PkgSig bundle witnessRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                      hsame row localityRead ∨ hsame row witnessRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont locality transport localityRead ∧
                    Cont localityRead name witnessRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle witnessRead pkg)
                hsame ∧
              UnaryHistory localityRead ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localityTransportRead localityNameWitness witnessPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
    localityUnary, _gapUnary, transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    _namePkg⟩ := carrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary transportUnary localityTransportRead
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed localityReadUnary nameUnary localityNameWitness
  have sourceWitness :
      (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row) witnessRead :=
    ⟨hsame_refl witnessRead, witnessReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row locality ∨ hsame row gap ∨ hsame row transport ∨ hsame row route ∨
              hsame row provenance ∨ hsame row name ∨ hsame row localityRead ∨
                hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont locality transport localityRead ∧
              Cont localityRead name witnessRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle witnessRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead sourceWitness
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localityTransportRead, localityNameWitness, provenancePkg, witnessPkg⟩
  }
  exact ⟨cert, localityReadUnary, witnessReadUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp

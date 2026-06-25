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

theorem ObserverPerspectiveClassifierObligationUnblockPackage [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name unblockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont transport route unblockRead →
        PkgSig bundle unblockRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row unblockRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observerLeft ∨ hsame row observerRight ∨
                  hsame row universeLeft ∨ hsame row universeRight ∨
                    hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                      hsame row route ∨ hsame row unblockRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont transport route unblockRead ∧
                  PkgSig bundle unblockRead pkg)
              hsame ∧
            UnaryHistory unblockRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier unblockRoute unblockPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      _localityUnary, _gapUnary, transportUnary, routeUnary, _provenanceUnary,
      _nameUnary, _observerUniverse, _universeLocality, _localityTransport,
      _transportGap, _provenancePkg, _namePkg⟩ := carrier
  have unblockUnary : UnaryHistory unblockRead :=
    unary_cont_closed transportUnary routeUnary unblockRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row unblockRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
              hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                hsame row transport ∨ hsame row route ∨ hsame row unblockRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport route unblockRead ∧
              PkgSig bundle unblockRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro unblockRead
        ⟨hsame_refl unblockRead, unblockUnary⟩
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
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, unblockRoute, unblockPkg⟩
  }
  exact ⟨cert, unblockUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp

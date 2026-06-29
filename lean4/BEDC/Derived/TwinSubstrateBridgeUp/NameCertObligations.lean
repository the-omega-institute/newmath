import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TwinSubstrateBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateBridgeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M G F R L H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory G →
        UnaryHistory F →
          UnaryHistory R →
            UnaryHistory L →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont M G R →
                        Cont R L endpoint →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              PkgSig bundle endpoint pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row endpoint ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row G ∨ hsame row F ∨
                                        hsame row R ∨ hsame row L ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                                            hsame row endpoint)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont M G R ∧
                                        Cont R L endpoint ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg ∧
                                            PkgSig bundle endpoint pkg)
                                    hsame ∧
                                  UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro mUnary gUnary _fUnary rUnary lUnary _hUnary _cUnary _pUnary _nUnary
    metaGroundRoute routeEndpoint provenancePkg namePkg endpointPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rUnary lUnary routeEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row F ∨ hsame row R ∨ hsame row L ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M G R ∧ Cont R L endpoint ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint
        ⟨hsame_refl endpoint, endpointUnary⟩
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
                    (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metaGroundRoute, routeEndpoint, provenancePkg, namePkg,
          endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.TwinSubstrateBridgeUp

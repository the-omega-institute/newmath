import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactMetricModulusRealizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactMetricModulusRealizerCarrier_finite_net_fold [AskSetup] [PackageSetup]
    {K F B L M T E U H C P N netRead modulusRead toleranceRead sealRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont K F netRead →
      Cont netRead B modulusRead →
        Cont modulusRead T toleranceRead →
          Cont toleranceRead E sealRead →
            Cont sealRead U exportRead →
              UnaryHistory K →
                UnaryHistory F →
                  UnaryHistory B →
                    UnaryHistory T →
                      UnaryHistory E →
                        UnaryHistory U →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row exportRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row K ∨ hsame row F ∨ hsame row B ∨
                                      hsame row L ∨ hsame row M ∨ hsame row T ∨
                                        hsame row E ∨ hsame row U ∨ hsame row P ∨
                                          hsame row N ∨ hsame row exportRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont K F netRead ∧
                                      Cont netRead B modulusRead ∧
                                        Cont modulusRead T toleranceRead ∧
                                          Cont toleranceRead E sealRead ∧
                                            Cont sealRead U exportRead ∧
                                              PkgSig bundle P pkg ∧
                                                PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory netRead ∧
                                  UnaryHistory modulusRead ∧
                                    UnaryHistory toleranceRead ∧
                                      UnaryHistory sealRead ∧
                                        UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro netRoute modulusRoute toleranceRoute sealRoute exportRoute kUnary fUnary bUnary tUnary
    eUnary uUnary provenancePkg namePkg
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed kUnary fUnary netRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed netUnary bUnary modulusRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary tUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed sealUnary uUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row M ∨
              hsame row T ∨ hsame row E ∨ hsame row U ∨ hsame row P ∨ hsame row N ∨
                hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F netRead ∧ Cont netRead B modulusRead ∧
              Cont modulusRead T toleranceRead ∧ Cont toleranceRead E sealRead ∧
                Cont sealRead U exportRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, netRoute, modulusRoute, toleranceRoute, sealRoute, exportRoute,
            provenancePkg, namePkg⟩
    }
  exact ⟨cert, netUnary, modulusUnary, toleranceUnary, sealUnary, exportUnary⟩

end BEDC.Derived.CompactMetricModulusRealizerUp

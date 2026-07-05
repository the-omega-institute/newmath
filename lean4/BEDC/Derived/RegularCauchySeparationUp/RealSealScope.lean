import BEDC.Derived.RegularCauchySeparationUp.NameCertObligations

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_real_seal_scope [AskSetup] [PackageSetup]
    {L R W D M E H C P N leftWindow rightWindow toleranceRead modulusRead sealRead
      supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory M ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont L W leftWindow ->
                          Cont R W rightWindow ->
                            Cont leftWindow D toleranceRead ->
                              Cont toleranceRead M modulusRead ->
                                Cont modulusRead E sealRead ->
                                  Cont sealRead H supportRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        PkgSig bundle supportRead pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row supportRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row L ∨ hsame row R ∨ hsame row W ∨
                                                  hsame row D ∨ hsame row M ∨ hsame row E ∨
                                                    hsame row H ∨ hsame row C ∨
                                                      hsame row P ∨ hsame row N ∨
                                                        hsame row sealRead ∨
                                                          hsame row supportRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont modulusRead E sealRead ∧
                                                  Cont sealRead H supportRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory leftWindow ∧
                                              UnaryHistory rightWindow ∧
                                                UnaryHistory toleranceRead ∧
                                                  UnaryHistory modulusRead ∧
                                                    UnaryHistory sealRead ∧
                                                      UnaryHistory supportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary supportUnary
    _transportUnary _provenanceUnary _nameUnary leftRoute rightRoute toleranceRoute modulusRoute
    sealRoute supportRoute provenancePkg namePkg _supportPkg
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary windowUnary leftRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed rightUnary windowUnary rightRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed leftWindowUnary dyadicUnary toleranceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary modulusUnary modulusRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusReadUnary sealUnary sealRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed sealReadUnary supportUnary supportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row M ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row sealRead ∨
                  hsame row supportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulusRead E sealRead ∧ Cont sealRead H supportRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro supportRead ⟨hsame_refl supportRead, supportReadUnary⟩
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, supportRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, leftWindowUnary, rightWindowUnary, toleranceUnary, modulusReadUnary,
      sealReadUnary, supportReadUnary⟩

end BEDC.Derived.RegularCauchySeparationUp
